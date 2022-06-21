use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Field, Fields};
use darling::{Error, util::Flag, FromDeriveInput, FromField, FromVariant};

// TODO: Maybe collect errors?

macro_rules! darling_unwrap {
    ($e:expr) => {
        match $e {
            Ok(v) => v,
            Err(e) => return e.write_errors().into(),
        }
    }
}

#[derive(FromDeriveInput, Default)]
#[darling(default, attributes(howmuchwhere))]
struct TopLevelOpts {
    __hmw_internal_use: Flag,
    via_size_of_val: Flag,
    via_size_of: Flag,
    statically_known: Flag,
    opaque_all_inline: Flag,
    override_repr: Option<Ident>,
    ignore_repr: Flag,
}

#[derive(FromVariant, Default)]
#[darling(default, attributes(howmuchwhere))]
struct VariantOpts {
    rename: Option<Ident>,
}

#[derive(FromField, Default)]
#[darling(default, attributes(howmuchwhere))]
struct FieldOpts {
    rename: Option<Ident>,
    via_size_of_val: Flag,
    via_size_of: Flag,
    statically_known: Flag,
    category: Option<Ident>,
    unsafe_follow: Flag,
}

fn derive_inner(
    item: TokenStream,
    derived: TokenStream2,
    method: &dyn Fn(TokenStream2, TokenStream2) -> TokenStream2,
    allow_nonstatic: bool,
) -> TokenStream {
    let item: DeriveInput = parse_macro_input!(item);
    let opts = darling_unwrap!(TopLevelOpts::from_derive_input(&item));

    let ident = item.ident;
    let crate_ = if opts.__hmw_internal_use.is_present() {
        quote!{ crate }
    } else {
        quote!{ ::howmuchwhere }
    };

    let collector = quote!{ collector };

    let opaque_impl = || quote!{
        collector.collect_in_manual_struct::<Self>()
            .field_const_size("data", ::core::mem::size_of::<Self>(), 0);
    };

    let struct_impl = |source, access_prefix, fields| {
        fn inner(
            crate_: &TokenStream2,
            opts: &TopLevelOpts,
            allow_nonstatic: bool,
            source: TokenStream2,
            access_prefix: TokenStream2,
            single_unnamed: bool,
            fields: impl Iterator<Item = (TokenStream2, Field)>
        ) -> darling::Result<TokenStream2> {
            let fields: Vec<TokenStream2> =
                fields
                    .map(|(name, field)| FieldOpts::from_field(&field).map(|field_opts| {
                        let field_name = match field_opts.rename {
                            None if single_unnamed => quote!{ wrapped },
                            None => name.clone(),
                            Some(renamed) => quote!{ #renamed },
                        };
                        let field_name = quote!{ stringify!(#field_name) };

                        enum Mode {
                            Normal,
                            SizeOfVal,
                            SizeOf,
                            StaticallyKnown,
                            UnsafeFollow,
                            UnsafeFollowSizeOfVal,
                        }

                        let (blame, mode) = if field_opts.unsafe_follow.is_present() {
                            if field_opts.via_size_of_val.is_present() {
                                (&field_opts.via_size_of_val, Mode::UnsafeFollowSizeOfVal)
                            } else if opts.via_size_of_val.is_present() {
                                (&opts.via_size_of_val, Mode::UnsafeFollowSizeOfVal)
                            } else {
                                (&field_opts.unsafe_follow, Mode::UnsafeFollow)
                            }
                        } else if field_opts.via_size_of_val.is_present() {
                            (&field_opts.via_size_of_val, Mode::SizeOfVal)
                        } else if field_opts.via_size_of.is_present() {
                            (&field_opts.via_size_of, Mode::SizeOf)
                        } else if field_opts.statically_known.is_present() {
                            (&field_opts.statically_known, Mode::StaticallyKnown)
                        } else if opts.via_size_of_val.is_present() {
                            (&opts.via_size_of_val, Mode::SizeOfVal)
                        } else if opts.via_size_of.is_present() {
                            (&opts.via_size_of, Mode::SizeOf)
                        } else if opts.statically_known.is_present() {
                            (&opts.statically_known, Mode::StaticallyKnown)
                        } else {
                            // the blame can be anything as we can't know within the proc macro if
                            // normal access will fail anyway
                            (&opts.__hmw_internal_use, Mode::Normal)
                        };

                        let access = quote!{ & #access_prefix #name };
                        let followptr = quote!{ unsafe { &* #access_prefix #name } };
                        let ty = field.ty;

                        let out = match mode {
                            Mode::Normal if allow_nonstatic =>
                                quote!{ .field(#crate_::Inline, #field_name, #access) },
                            Mode::Normal => quote!{
                                .field_statically_known::<#ty>(#crate_::Inline, #field_name)
                            },
                            Mode::SizeOfVal if allow_nonstatic =>
                                quote!{ .field_size_of_val(#crate_::Inline, #field_name, #access) },
                            Mode::SizeOf => quote!{
                                .field_const_size(#field_name, ::core::mem::size_of::<#ty>(), 0)
                            },
                            Mode::StaticallyKnown => quote!{
                                .field_statically_known::<#ty>(#crate_::Inline, #field_name)
                            },
                            Mode::UnsafeFollow if allow_nonstatic => quote!{
                                .field_const_size(#field_name, ::core::mem::size_of::<#ty>(), 0)
                                .field(#crate_::Allocated, #field_name, #followptr)
                            },
                            Mode::UnsafeFollow => quote!{
                                .field_const_size(#field_name, ::core::mem::size_of::<#ty>(), 0)
                                .field_statically_known::<#ty>(#crate_::Allocated, #field_name)
                            },
                            Mode::UnsafeFollowSizeOfVal if allow_nonstatic => quote!{
                                .field_const_size(#field_name, ::core::mem::size_of::<#ty>(), 0)
                                .field_size_of_val(#crate_::Allocated, #field_name, #followptr)
                            },
                            _ => {
                                return Error::custom(
                                    "Cannot be used in a statically known only context"
                                )
                                    .with_span(blame)
                                    .write_errors()
                                    .into();
                            },
                        };

                        match field_opts.category {
                            None => out,
                            Some(category) => quote!{
                                .category(stringify!(#category), |c| c #out.end_ref())
                            },
                        }
                    }))
                    .collect::<Result<_, _>>()?;

            Ok(
                quote!{
                    #source #(#fields)*;
                }
            )
        }

        match fields {
            Fields::Named(named) => inner(
                &crate_,
                &opts,
                allow_nonstatic,
                source,
                access_prefix,
                false,
                named.named.into_iter()
                    .map(|mut f| {
                        let ident = f.ident.take();
                        (quote!{ #ident }, f)
                    })
            ),
            Fields::Unnamed(unnamed) => inner(
                &crate_,
                &opts,
                allow_nonstatic,
                source,
                access_prefix,
                unnamed.unnamed.len() == 1,
                unnamed.unnamed.into_iter().enumerate().map(|(i, f)| (format!("{i}").parse().unwrap(), f))
            ),
            Fields::Unit =>
                inner(&crate_, &opts, allow_nonstatic, source, access_prefix, false, std::iter::empty()),
        }
    };

    let output = if opts.opaque_all_inline.is_present() {
        opaque_impl()
    } else {
        match item.data {
            Data::Struct(struct_) => match struct_.fields {
                Fields::Unit => opaque_impl(),
                fields => darling_unwrap!(
                    struct_impl(
                        quote!{ #collector.collect_in_struct::<Self>() },
                        quote!{ self. },
                        fields
                    )
                ),
            },
            Data::Enum(enum_) if enum_.variants.is_empty() => opaque_impl(),
            Data::Enum(enum_) if enum_.variants.iter().all(|i| i.fields == Fields::Unit) =>
                opaque_impl(),
            Data::Enum(enum_) => {
                #[derive(Debug)]
                enum Repr {
                    C,
                    Ty(Ident),
                }

                let tag_size = match opts.override_repr {
                    Some(ref repr) => quote!{ Some(::core::mem::size_of::<#repr>()) },
                    None if opts.ignore_repr.is_present() => quote!{ None },
                    None => {
                        let repr = item.attrs.iter()
                            .filter(|i| i.path.is_ident("repr"))
                            .filter_map(|i| {
                                use syn::parse::Parser;

                                fn parse_repr_arg(input: syn::parse::ParseStream) -> syn::Result<Option<Repr>> {
                                    let content;
                                    syn::parenthesized!(content in input);
                                    let out = content.parse()?;
                                    if out == "C" {
                                        Ok(Some(Repr::C))
                                    } else if out == "Rust" {
                                        Ok(None)
                                    } else {
                                        Ok(Some(Repr::Ty(out)))
                                    }
                                }

                                parse_repr_arg.parse2(i.tokens.clone()).ok().flatten()
                            })
                            .reduce(|l, r| match l {
                                Repr::C => r,
                                Repr::Ty(_) => l,
                            });

                        match repr {
                            None => quote!{ None },
                            Some(Repr::C) => quote!{ Some(::core::mem::size_of::<::std::os::raw::c_int>()) },
                            Some(Repr::Ty(name)) => quote!{ Some(::core::mem::size_of::<#name>()) },
                        }
                    }
                };

                let variants: Vec<_> = darling_unwrap!(
                    enum_.variants.into_iter()
                        .map(|variant| {
                            let variant_opts = VariantOpts::from_variant(&variant)?;
                            let variantname = match variant_opts.rename {
                                None => variant.ident,
                                Some(renamed) => renamed,
                            };
                            let (matcher, match_fixer, prefix) = match variant.fields {
                                Fields::Named(ref named) => {
                                    let named = named.named.iter().map(|i| i.ident.clone().unwrap());
                                    (quote!{ { #( ref #named ),* } }, quote!{ }, quote!{ * })
                                },
                                Fields::Unnamed(ref unnamed) => {
                                    let named = (0..unnamed.unnamed.len())
                                        .map(|i| format!("x{i}").parse::<TokenStream2>().unwrap())
                                        .collect::<Vec<_>>();
                                    (
                                        quote!{ ( #( ref #named ),* ) },
                                        quote!{ let fixed = ( #( #named, )* ); },
                                        quote!{ *fixed. }
                                    )
                                },
                                Fields::Unit => (quote!{ }, quote!{ }, quote!{ }),
                            };

                            let source = quote!{
                                #collector.collect_in_variant::<Self>(
                                    ::core::stringify!(#variantname),
                                    #tag_size
                                )
                            };

                            let out = match struct_impl(source, prefix, variant.fields) {
                                Ok(out) => out,
                                Err(err) => return Err(err),
                            };

                            Ok(quote!{
                                #ident::#variantname #matcher => {
                                    #match_fixer

                                    #out
                                }
                            })
                        })
                        .collect()
                );

                quote!{
                    match *self {
                        #(#variants)*
                    }
                }
            },
            Data::Union(union_) =>
                return TokenStream::from(
                    Error::custom("HowMuchWhere cannot be automatically derived for `union`s")
                        .with_span(&union_.union_token)
                        .write_errors()
                ),
        }
    };

    let method = method(collector, crate_.clone());
    let (impl_generics, ty_generics, where_clause) = item.generics.split_for_impl();
    let output = quote!{
        impl #impl_generics #crate_::#derived for #ident #ty_generics #where_clause {
            #method {
                #output
            }
        }
    };

    output.into()
}

#[proc_macro_derive(HowMuchWhere, attributes(howmuchwhere))]
pub fn derive_how_much_where(item: TokenStream) -> TokenStream {
    derive_inner(
        item,
        quote!{ HowMuchWhere },
        &|collector, crate_| quote!{
            fn how_much_where_impl(&self, #collector: &mut #crate_::Collector)
        },
        true
    )
}

#[proc_macro_derive(StaticallyKnown, attributes(howmuchwhere))]
pub fn derive_statically_known(item: TokenStream) -> TokenStream {
    derive_inner(
        item,
        quote!{ StaticallyKnown },
        &|collector, crate_| quote!{
            fn how_much_where_impl_static(#collector: &mut #crate_::Collector)
        },
        false
    )
}
