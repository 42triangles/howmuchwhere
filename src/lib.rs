use std::alloc::Layout;
use std::cmp::max;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::num::NonZeroUsize;
use std::ops;

pub use howmuchwhere_derive::{HowMuchWhere, StaticallyKnown};

#[cfg(test)]
mod test;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, HowMuchWhere, StaticallyKnown,
)]
#[howmuchwhere(__hmw_internal_use)]
pub enum Kind {
    Type,
    Variant,
    Category,
    Field,
}

pub type Path = Vec<(Kind, &'static str)>;

fn shorten_type(name: &str) -> &str {
    name.split('<').next().unwrap().rsplit("::").next().unwrap()
}

pub fn format_path(path: &Path) -> String {
    let mut out = String::new();
    for &(k, n) in path {
        match k {
            Kind::Type => out += " >>",
            Kind::Variant => out += "::",
            Kind::Category => out += "#",
            Kind::Field => out += ".",
        }
        if k == Kind::Type {
            out += shorten_type(n);
        } else {
            out += n;
        }
    }

    return out;
}

pub type Collection = HashMap<Path, usize>;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, HowMuchWhere, StaticallyKnown,
)]
#[howmuchwhere(__hmw_internal_use, opaque_all_inline)]
pub struct OpaquePointer(NonZeroUsize);

impl OpaquePointer {
    pub fn from_usize(x: NonZeroUsize) -> Self {
        OpaquePointer(x)
    }

    pub fn from_ptr<T: ?Sized>(ptr: *const T) -> Self {
        let ptr = ptr as *const u8;
        assert!(ptr != std::ptr::null());
        OpaquePointer(NonZeroUsize::try_from(ptr as usize).unwrap())
    }
}

pub type GeneralPath = (Option<OpaquePointer>, Path);

#[derive(Clone, PartialEq, Eq, HowMuchWhere)]
#[howmuchwhere(__hmw_internal_use)]
pub struct CollectionResult {
    pub root: Collection,
    pub shared: HashMap<OpaquePointer, (Vec<GeneralPath>, Collection)>,
}

impl CollectionResult {
    pub fn total_size(&self) -> usize {
        self.root.values().copied().sum::<usize>()
            + self
                .shared
                .values()
                .map(|i| i.1.values().copied().sum::<usize>())
                .sum::<usize>()
    }
}

impl std::fmt::Debug for CollectionResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CollectionResult {{\n")?;
        for (k, &v) in self.root.iter() {
            write!(f, "{} => {v}\n", format_path(k))?;
        }

        if !self.shared.is_empty() {
            write!(f, "\n\n")?;
        }

        for (&opaque, &(ref anchors, ref coll)) in self.shared.iter() {
            write!(f, "{:x}:\n", opaque.0)?;
            for (other, path) in anchors {
                write!(f, "  anchor ")?;
                if let Some(other) = other {
                    write!(f, "@{:x} ", other.0)?;
                }
                write!(f, "{}\n", format_path(path))?;
            }
            write!(f, "  ----\n")?;
            for (k, &v) in coll.iter() {
                write!(f, "  {} => {v}\n", format_path(k))?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

#[derive(HowMuchWhere)]
#[howmuchwhere(__hmw_internal_use)]
pub struct Collector<'a> {
    #[howmuchwhere(category = "state")]
    parent_shared: Option<OpaquePointer>,
    #[howmuchwhere(category = "state")]
    current_prefix: Path,
    #[howmuchwhere(category = "data")]
    data: Collection,
    #[howmuchwhere(category = "data")]
    shared: &'a mut HashMap<OpaquePointer, (Vec<GeneralPath>, Collection)>,
}

impl<'a> Collector<'a> {
    fn new(
        parent_shared: Option<OpaquePointer>,
        shared: &'a mut HashMap<OpaquePointer, (Vec<GeneralPath>, Collection)>,
    ) -> Self {
        Collector {
            parent_shared,
            current_prefix: Vec::new(),
            data: HashMap::new(),
            shared,
        }
    }

    pub fn collect_shared<T: ?Sized>(&mut self, pointer: *const T, f: impl FnOnce(&mut Collector)) {
        let pointer = OpaquePointer::from_ptr(pointer);

        let mut has_to_fill = false;
        self.shared
            .entry(pointer)
            .or_insert_with(|| {
                has_to_fill = true;
                (Vec::with_capacity(1), HashMap::new())
            })
            .0
            .push((self.parent_shared, self.current_prefix.clone()));

        if has_to_fill {
            let mut collector = Collector::new(Some(pointer), self.shared);
            f(&mut collector);
            self.shared.get_mut(&pointer).unwrap().1 = collector.data;
        }
    }

    fn collect_struct_with<T: ?Sized>(&mut self, size: usize) -> StructCollector<'a, '_> {
        self.current_prefix
            .push((Kind::Type, std::any::type_name::<T>()));

        StructCollector {
            collector: self,
            full_size: size,
            seen_size: 0,
            mode: StructMode::Struct,
        }
    }

    pub fn collect_in_manual_struct<T: ?Sized>(&mut self) -> StructCollector<'a, '_> {
        self.collect_struct_with::<T>(0)
    }

    pub fn collect_in_unsized_struct<T: ?Sized>(&mut self, value: &T) -> StructCollector<'a, '_> {
        self.collect_struct_with::<T>(mem::size_of_val(value))
    }

    pub fn collect_in_struct<T: Sized>(&mut self) -> StructCollector<'a, '_> {
        self.collect_struct_with::<T>(mem::size_of::<T>())
    }

    fn collect_variant_with<T: ?Sized>(
        &mut self,
        variant: &'static str,
        size: usize,
        mode: StructMode,
    ) -> VariantCollector<'a, '_> {
        self.current_prefix
            .push((Kind::Type, std::any::type_name::<T>()));
        self.current_prefix.push((Kind::Variant, variant));

        VariantCollector(StructCollector {
            collector: self,
            full_size: size,
            seen_size: 0,
            mode,
        })
    }

    pub fn collect_in_manual_variant<T: ?Sized>(
        &mut self,
        variant: &'static str,
    ) -> VariantCollector<'a, '_> {
        self.collect_variant_with::<T>(variant, 0, StructMode::VariantKnownTag)
    }

    /// When using this please do take optimisations into account that might allocate values for
    /// the tag through impossible values inside wrapping variants; as well as padding.
    ///
    /// If the `enum` isn't `#[repr(uint_ty)]`, `tag_size` should be `0`
    pub fn collect_in_variant<T: Sized>(
        &mut self,
        variant: &'static str,
        tag_size: Option<usize>,
    ) -> VariantCollector<'a, '_> {
        let mut out = self.collect_variant_with::<T>(
            variant,
            mem::size_of::<T>(),
            match tag_size {
                Some(_) => StructMode::VariantKnownTag,
                None => StructMode::VariantUnknownTag,
            },
        );

        if let Some(tag_size) = tag_size {
            out.category("overhead", |c| {
                c.field_const_size("tag_size", tag_size, 0).end_ref()
            });
        }

        out
    }

    fn push_field_inner(&mut self, size: usize) {
        if size == 0 {
            return;
        }

        if let Some(count) = self.data.get_mut(&self.current_prefix) {
            *count = count.checked_add(size).unwrap();
        } else {
            // Double lookups aren't too much of an issue here as this path is rather unlikely for
            // anything but (singly) linked lists and such
            self.data.insert(self.current_prefix.clone(), size);
        }
    }
}

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash, Debug, HowMuchWhere, StaticallyKnown,
)]
#[howmuchwhere(__hmw_internal_use)]
pub enum Location {
    #[default]
    Inline,
    Allocated,
    Shared,
}

pub use Location::*;

#[derive(Clone, HowMuchWhere, StaticallyKnown)]
#[howmuchwhere(__hmw_internal_use)]
enum StructMode {
    Struct,
    VariantKnownTag,
    VariantUnknownTag,
}

#[derive(HowMuchWhere, StaticallyKnown)]
#[howmuchwhere(__hmw_internal_use)]
pub struct StructCollector<'a: 'b, 'b> {
    collector: &'b mut Collector<'a>,
    #[howmuchwhere(category = "detect_padding")]
    full_size: usize,
    #[howmuchwhere(category = "detect_padding")]
    seen_size: usize,
    #[howmuchwhere(category = "detect_padding")]
    mode: StructMode,
}

impl StructCollector<'_, '_> {
    pub fn field_generic(
        &mut self,
        name: &'static str,
        shared: Option<*const u8>,
        f: impl FnOnce(&mut Collector),
    ) -> &mut Self {
        self.collector.current_prefix.push((Kind::Field, name));
        match shared {
            None => f(&mut self.collector),
            Some(ptr) => self.collector.collect_shared(ptr, f),
        }
        self.collector.current_prefix.pop();
        self
    }

    pub fn field_generic_shared<T: ?Sized>(
        &mut self,
        name: &'static str,
        shared: *const T,
        f: impl FnOnce(&mut Collector),
    ) -> &mut Self {
        self.field_generic(name, Some(shared as *const u8), f)
    }

    pub fn ignore_size_chunk(&mut self, chunk: usize) -> &mut Self {
        self.seen_size = self.seen_size.checked_add(chunk).unwrap();
        self
    }

    pub fn field(
        &mut self,
        loc: Location,
        name: &'static str,
        field: &(impl HowMuchWhere + ?Sized),
    ) -> &mut Self {
        match loc {
            Inline => {
                self.seen_size = self.seen_size.checked_add(mem::size_of_val(field)).unwrap();
                self.field_generic(name, None, |this| field.how_much_where_impl(this))
            }
            Allocated => self.field_generic(name, None, |this| field.how_much_where_impl(this)),
            Shared => {
                self.field_generic_shared(name, field, |this| field.how_much_where_impl(this))
            }
        }
    }

    pub fn shared_field_via<T: ?Sized>(
        &mut self,
        name: &'static str,
        shared: *const T,
        field: &(impl HowMuchWhere + ?Sized),
    ) -> &mut Self {
        self.field_generic_shared(name, shared, |this| field.how_much_where_impl(this))
    }

    pub fn field_const_size(
        &mut self,
        name: &'static str,
        inline_size: usize,
        alloc_size: usize,
    ) -> &mut Self {
        self.seen_size += inline_size;
        self.field_generic(name, None, |this| {
            this.push_field_inner(inline_size.checked_add(alloc_size).unwrap())
        })
    }

    pub fn field_shared_const_size<T: ?Sized>(
        &mut self,
        name: &'static str,
        shared: *const T,
        size: usize,
    ) -> &mut Self {
        self.field_generic_shared(name, shared, |this| this.push_field_inner(size))
    }

    pub fn field_size_of_val<T: ?Sized>(
        &mut self,
        loc: Location,
        name: &'static str,
        field: &T,
    ) -> &mut Self {
        let size = mem::size_of_val(field);
        match loc {
            Inline => self.field_const_size(name, size, 0),
            Allocated => self.field_const_size(name, 0, size),
            Shared => self.field_generic_shared(name, field, |this| this.push_field_inner(size)),
        }
    }

    pub fn field_statically_known<T: StaticallyKnown>(
        &mut self,
        loc: Location,
        name: &'static str,
    ) -> &mut Self {
        if loc == Inline {
            self.seen_size += mem::size_of::<T>();
        }
        assert!(loc != Shared);
        self.field_generic(name, None, |this| T::how_much_where_impl_static(this))
    }

    pub fn category(&mut self, name: &'static str, f: impl FnOnce(&mut Self)) -> &mut Self {
        self.collector.current_prefix.push((Kind::Category, name));
        f(self);
        self.collector.current_prefix.pop();
        self
    }

    pub fn with_ref(&mut self, f: impl FnOnce(&mut Self)) -> &mut Self {
        f(self);
        self
    }

    pub fn end_ref(&mut self) {}

    fn push_padding(&mut self) {
        if self.seen_size < self.full_size {
            let mode = self.mode.clone();
            let diff = self.full_size - self.seen_size;

            self.category("overhead", |c| {
                c.field_const_size(
                    match mode {
                        StructMode::Struct => "internal_padding",
                        StructMode::VariantKnownTag => "internal_padding_and_unused",
                        StructMode::VariantUnknownTag => "internal_tag_padding_and_unused",
                    },
                    diff,
                    0,
                )
                .end_ref()
            });

            self.seen_size = self.full_size;
        }
    }
}

impl Drop for StructCollector<'_, '_> {
    fn drop(&mut self) {
        self.push_padding();

        self.collector.current_prefix.pop();
    }
}

#[derive(HowMuchWhere, StaticallyKnown)]
#[howmuchwhere(__hmw_internal_use)]
pub struct VariantCollector<'a: 'b, 'b>(StructCollector<'a, 'b>);

impl<'a, 'b> ops::Deref for VariantCollector<'a, 'b> {
    type Target = StructCollector<'a, 'b>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for VariantCollector<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Drop for VariantCollector<'_, '_> {
    fn drop(&mut self) {
        self.push_padding(); // The padding has to be pushed before the variant is left

        self.collector.current_prefix.pop();
    }
}

fn finalise(run: impl Fn(&mut Collector)) -> CollectionResult {
    let mut shared = HashMap::new();
    let mut collector = Collector::new(None, &mut shared);

    run(&mut collector);

    let mut data = collector.data;

    // This is... Not an efficient way to go about it, but it's difficult to actually do it
    // efficiently because this needs to be able to modify the `shared` HashMap while reading from
    // it.
    // And we don't want to visit things twice ideally, either.
    let pointers = shared.keys().copied().collect::<Vec<_>>();

    for i in pointers {
        let &mut (ref mut paths, ref mut shared_data) = shared.get_mut(&i).unwrap();

        let mut removed = false;

        if shared_data.is_empty() {
            shared.remove(&i);
            removed = true;
        } else if paths.len() != 1 {
            // Keep it as is
        } else {
            let (paths, shared_data) = shared.remove(&i).unwrap();
            removed = true;

            let (path_anchor, path) = paths.into_iter().next().unwrap();
            let collection = match path_anchor {
                None => &mut data,
                Some(ptr) =>
                // The pointer is always in `shared` (unless there's a bug), since for an entry
                // to have been removed before it would have to be empty (in which case it
                // cannot contain anything to reference this) or only have one anchor (in which
                // case only a cycle could cause this, but since we collect from a root object,
                // a cycle where each part is only anchored in another part of the cycle is not
                // possible).
                {
                    &mut shared.get_mut(&ptr).unwrap().1
                }
            };

            for (mut path_here, byte_count) in shared_data {
                path_here.splice(0..0, path.iter().copied());
                *collection.entry(path_here).or_insert(0) += byte_count;
            }
        }

        // We are potentially removing *A LOT* of things
        if removed {
            if shared.len() < shared.capacity() / 2 {
                shared.shrink_to_fit();
            }
        }
    }

    CollectionResult {
        root: data,
        shared: shared,
    }
}

pub trait HowMuchWhere {
    fn how_much_where_impl(&self, collector: &mut Collector);

    fn how_much_where(&self) -> CollectionResult {
        finalise(|collector| self.how_much_where_impl(collector))
    }
}

pub trait StaticallyKnown: HowMuchWhere + Sized {
    fn how_much_where_impl_static(collector: &mut Collector);

    fn how_much_where_static() -> CollectionResult {
        finalise(Self::how_much_where_impl_static)
    }
}

mod sealed {
    pub trait FollowMode {
        const LOC: super::Location;
    }
}

pub trait FollowMode: sealed::FollowMode {}

pub struct SharedFollow;
impl sealed::FollowMode for SharedFollow {
    const LOC: Location = Shared;
}
impl FollowMode for SharedFollow {}

pub struct UniqueFollow;
impl sealed::FollowMode for UniqueFollow {
    const LOC: Location = Allocated;
}
impl FollowMode for UniqueFollow {}

pub struct Follow<'a, T: ?Sized, Mode: FollowMode>(pub &'a T, std::marker::PhantomData<Mode>);

impl<'a, T: ?Sized, M: FollowMode> Follow<'a, T, M> {
    pub fn from_ref(x: &'a &T) -> Self {
        Follow(*x, std::marker::PhantomData)
    }

    pub fn from_ref_mut(x: &'a &mut T) -> Self {
        Follow(*x, std::marker::PhantomData)
    }

    pub unsafe fn from_ptr(x: &'a *const T) -> Self {
        Follow(&**x, std::marker::PhantomData)
    }

    pub unsafe fn from_ptr_mut(x: &'a *mut T) -> Self {
        Follow(&**x, std::marker::PhantomData)
    }
}

impl<T: ?Sized + HowMuchWhere, M: FollowMode> HowMuchWhere for Follow<'_, T, M> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<&T>(), 0)
                    .end_ref()
            })
            .field(M::LOC, "referenced", &*self.0);
    }
}

impl<'a, T: ?Sized + StaticallyKnown + 'a> StaticallyKnown for Follow<'a, T, UniqueFollow> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<&T>(), 0)
                    .end_ref()
            })
            .field_statically_known::<T>(Allocated, "referenced");
    }
}

fn collection_data_without_padding<'a, T: HowMuchWhere + ?Sized + 'a>(
    loc: Location,
    t: impl IntoIterator<Item = &'a T>,
    collector: &mut StructCollector<'_, '_>,
) {
    for i in t {
        collector.field(loc, "data", i);
    }
}

fn cumulative_padding<T>(len: usize) -> usize {
    let layout = Layout::new::<T>();
    (layout.pad_to_align().size() - layout.size()) * len
}

fn slicelike_collection<'a, T: HowMuchWhere + Sized + 'a, C: ?Sized>(
    value: &'a C,
    collector: &mut Collector<'_>,
) where
    &'a C: IntoIterator<Item = &'a T>,
{
    let mut collector = collector.collect_in_unsized_struct(value);
    collection_data_without_padding(Inline, value, &mut collector);
}

fn veclike_collection<'a, T: HowMuchWhere + 'a, C: ?Sized>(
    value: &'a C,
    len: usize,
    capacity: usize,
    collector: &mut Collector<'_>,
) where
    &'a C: IntoIterator<Item = &'a T>,
{
    let mut collector = collector.collect_in_manual_struct::<C>();
    collector.category("overhead", |c| {
        c.field_size_of_val(Inline, "inline_overhead", value)
            .field_const_size(
                "unused_capacity",
                0,
                (capacity - len) * Layout::new::<T>().pad_to_align().size(),
            )
            .field_const_size("data_padding", 0, cumulative_padding::<T>(len))
            .end_ref()
    });
    collection_data_without_padding(Allocated, value, &mut collector);
}

fn collect_smart_ptr<C: ops::Deref<Target = T>, T: HowMuchWhere + ?Sized>(
    value: &C,
    collector: &mut Collector<'_>,
) {
    collector
        .collect_in_manual_struct::<C>()
        .category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", value)
                .end_ref()
        })
        .field(Allocated, "referenced", &**value);
}

fn collect_smart_ptr_static<C: ops::Deref>(collector: &mut Collector<'_>)
where
    C::Target: StaticallyKnown,
{
    collector
        .collect_in_manual_struct::<C>()
        .category("overhead", |c| {
            c.field_const_size("inline_overhead", mem::size_of::<C>(), 0)
                .end_ref()
        })
        .field_statically_known::<C::Target>(Allocated, "referenced");
}

impl<T: HowMuchWhere, const N: usize> HowMuchWhere for [T; N] {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        slicelike_collection(self, collector);
    }
}

impl<T: StaticallyKnown, const N: usize> StaticallyKnown for [T; N] {
    fn how_much_where_impl_static(collector: &mut Collector) {
        let mut collector = collector.collect_in_struct::<Self>();
        for _ in 0..N {
            collector.field_statically_known::<T>(Inline, "data");
        }
    }
}

impl<T: HowMuchWhere> HowMuchWhere for [T] {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        slicelike_collection(self, collector);
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::collections::BinaryHeap<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        veclike_collection(self, self.len(), self.capacity(), collector);
    }
}

/// # This implementation has issues
/// NOTE: Sadly it's impossible to retrieve the capacity of `IntoIter`
///
/// NOTE: This clones itself to access the member inside, which will however only provide a lower
/// bound for the actual memory consumption (or a completely incorrect one depending on the kinds
/// of types inside)
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::collections::binary_heap::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .field_const_size("unused_capacity_unknown", 0, 1)
                .end_ref()
        });

        // Sadly we can't access the data without cloning
        let mut len = 0usize;
        for i in self.clone() {
            collector.field(Allocated, "data", &i);
            len += 1;
        }

        collector.category("overhead", |c| {
            c.field_const_size("data_padding", 0, cumulative_padding::<T>(len))
                .end_ref()
        });
    }
}

fn apply_btree_info<K, V>(len: usize, collector: &mut StructCollector<'_, '_>) {
    // In the last checked implementation, B had a value of 6 and the layout was:
    //
    // for leaf nodes:
    // * parent: ptr
    // * parent_idx: u16
    // * len: u16
    // * keys: [K ; B*2 - 1]
    // * values: [V ; B*2 - 1]
    //
    // for internal nods, that, plus:
    // * edges [ptr ; 8*2]

    if len == 0 {
        return;
    }

    let b = 6usize;

    let nodes: usize = (len + 2 * b - 2) / (2 * b - 1);

    let (bulk, filled_rim) = 'height: loop {
        let mut bulk = 0;
        for bulk_height in 0.. {
            let nodes_for_height = bulk + (2 * b).pow(bulk_height);
            if nodes_for_height >= nodes {
                break 'height (bulk, nodes_for_height - bulk);
            }
            bulk = nodes_for_height;
        }
        unreachable!();
    };

    let outer_leaf_nodes = nodes - bulk;
    let inner_leaf_ndoes = (filled_rim - outer_leaf_nodes) / (2 * b);
    let leaf_nodes = inner_leaf_ndoes + outer_leaf_nodes;
    let internal_nodes = nodes - leaf_nodes;

    struct LeafNode<K, V> {
        _parent: *const u8,
        _parent_idx: u16,
        _len: u16,
        _keys: [K; 11],
        _vals: [V; 11],
    }

    let leaf_node_layout = Layout::new::<LeafNode<K, V>>();
    let internal_node_layout = leaf_node_layout
        .extend(Layout::new::<[*const u8; 12]>())
        .unwrap()
        .0;

    let padded_kv_size =
        Layout::new::<K>().pad_to_align().size() + Layout::new::<V>().pad_to_align().size();

    let overhead = |layout: Layout| layout.size() - 11 * padded_kv_size;

    collector.category("overhead", |c| {
        c.field_const_size(
            "alloc_overhead",
            0,
            overhead(leaf_node_layout) * leaf_nodes
                + overhead(internal_node_layout) * internal_nodes,
        )
        .field_const_size(
            "min_unused_capacity",
            0,
            padded_kv_size * (nodes * 11 - len),
        )
        .field_const_size(
            "min_data_padding",
            0,
            (nodes * 11) * (padded_kv_size - (mem::size_of::<K>() + mem::size_of::<V>())),
        )
        .end_ref()
    });
}

/// # This implementation has issues
/// NOTE: Sadly it's impossible to retrieve the unused capacity inside nodes, or the exact number
/// of nodes for that matter. This implementation assumes a fully packed tree.
///
/// For the node overhead it's just using the layout from the nightly std from 2022-06-19
impl<K: HowMuchWhere, V: HowMuchWhere> HowMuchWhere for std::collections::BTreeMap<K, V> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        apply_btree_info::<K, V>(self.len(), &mut collector);

        for (key, value) in self {
            collector.field(Allocated, "keys", key);
            collector.field(Allocated, "values", value);
        }
    }
}

/// # This implementation has issues
/// NOTE: Sadly it's impossible to retrieve the unused capacity inside nodes, or the exact number
/// of nodes for that matter. This implementation assumes a fully packed tree.
///
/// For the node overhead it's just using the layout from the nightly std from 2022-06-19
impl<T: HowMuchWhere> HowMuchWhere for std::collections::BTreeSet<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        apply_btree_info::<T, ()>(self.len(), &mut collector);

        for i in self {
            collector.field(Allocated, "data", i);
        }
    }
}

fn apply_hashmap_info<K, V>(len: usize, capacity: usize, collector: &mut StructCollector<'_, '_>) {
    let kv_layout = Layout::new::<(K, V)>().pad_to_align();

    let buckets = match capacity {
        0 => return,
        1..=3 => 4,
        4..=7 => 8,
        cap => ((cap * 8) / 7).next_power_of_two(),
    };

    let layout = Layout::from_size_align(
        kv_layout.size() * buckets + buckets + 128 / 8,
        max(kv_layout.align(), 128 / 8),
    )
    .unwrap()
    .pad_to_align();

    let padded_kv_size =
        Layout::new::<K>().pad_to_align().size() + Layout::new::<V>().pad_to_align().size();

    collector.category("overhead", |c| {
        c.field_const_size(
            "alloc_overhead",
            0,
            layout.size() - padded_kv_size * capacity,
        )
        .field_const_size("unused_capacity", 0, padded_kv_size * (capacity - len))
        .field_const_size(
            "data_padding",
            0,
            len * (padded_kv_size - mem::size_of::<K>() - mem::size_of::<V>()),
        )
        .end_ref()
    });
}

/// # This implementation has issues
/// NOTE: This is based on hashbrown v0.12.1, so this might be inaccurate for other versions, and
/// also assumes SSE2 to be available. If it isn't, this will be report a *slightly* bigger
/// allocated overhead
impl<K: HowMuchWhere, V: HowMuchWhere, S> HowMuchWhere for std::collections::HashMap<K, V, S> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();

        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        apply_hashmap_info::<K, V>(self.len(), self.capacity(), &mut collector);

        for (key, value) in self {
            collector.field(Allocated, "keys", key);
            collector.field(Allocated, "values", value);
        }
    }
}

/// # This implementation has issues
/// NOTE: This is based on hashbrown v0.12.1, so this might be inaccurate for other versions, and
/// also assumes SSE2 to be available. If it isn't, this will be report a *slightly* bigger
/// allocated overhead
impl<T: HowMuchWhere, S> HowMuchWhere for std::collections::HashSet<T, S> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();

        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        apply_hashmap_info::<T, ()>(self.len(), self.capacity(), &mut collector);

        for i in self {
            collector.field(Allocated, "data", i);
        }
    }
}

fn apply_linkedlist_info<'a, T>(len: usize, collector: &mut StructCollector) {
    struct Node<T> {
        _next: *const u8,
        _prev: *const u8,
        _element: T,
    }

    collector.category("overhead", |c| {
        c.field_const_size(
            "alloc_overhead",
            0,
            len * (mem::size_of::<Node<T>>() - mem::size_of::<T>()),
        )
        .end_ref()
    });
}

/// # This implementation has issues
/// NOTE: This is based on the nightly std from 2022-06-19
impl<T: HowMuchWhere> HowMuchWhere for std::collections::LinkedList<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();

        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        apply_linkedlist_info::<T>(self.len(), &mut collector);

        for i in self {
            collector.field(Allocated, "data", i);
        }
    }
}

/// # This implementation has issues
/// NOTE: This is based on the nightly std from 2022-06-19
///
/// NOTE: This relies on cloning itself to access the internal data, which means referenced data
/// that gets reallocated might have a different size
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::collections::linked_list::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();

        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .end_ref()
        });

        let mut len = 0usize;
        for i in self.clone() {
            collector.field(Allocated, "data", &i);
            len += 1;
        }

        apply_linkedlist_info::<T>(len, &mut collector);
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::collections::VecDeque<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        veclike_collection(self, self.len(), self.capacity(), collector)
    }
}

/// # This implementation has issues
/// NOTE: This relies on cloning itself to access the internal data, which means referenced data
/// that gets reallocated might have a different size, additionally the capacity is unknown
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::collections::vec_deque::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .field_const_size("unused_capacity_unknown", 0, 1)
                .end_ref()
        });

        // Sadly we can't access the data without cloning
        let mut len = 0usize;
        for i in self.clone() {
            collector.field(Allocated, "data", &i);
            len += 1;
        }

        collector.category("overhead", |c| {
            c.field_const_size("data_padding", 0, cumulative_padding::<T>(len))
                .end_ref()
        });
    }
}

impl<T: ?Sized> HowMuchWhere for &'_ T {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector)
    }
}

impl<'a, T: ?Sized + 'a> StaticallyKnown for &'a T {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_const_size("value", mem::size_of::<Self>(), 0);
    }
}

impl<T: ?Sized> HowMuchWhere for &'_ mut T {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector)
    }
}

impl<'a, T: ?Sized + 'a> StaticallyKnown for &'a mut T {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_const_size("value", mem::size_of::<Self>(), 0);
    }
}

impl<T: HowMuchWhere + ?Sized> HowMuchWhere for Box<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collect_smart_ptr(self, collector)
    }
}

impl<T: StaticallyKnown> StaticallyKnown for Box<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collect_smart_ptr_static::<Self>(collector)
    }
}

impl<T: HowMuchWhere + ?Sized + ToOwned> HowMuchWhere for std::borrow::Cow<'_, T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::borrow::Cow;
        match *self {
            Cow::Borrowed(_) => {
                collector
                    .collect_in_variant::<Self>("Borrowed", None)
                    .field_statically_known::<&T>(Inline, "reference");
            }
            Cow::Owned(_) => {
                collector
                    .collect_in_manual_variant::<Self>("Owned")
                    .category("overhead", |c| {
                        c.field_size_of_val(Inline, "inline_overhead", self)
                            .end_ref()
                    })
                    .field(Allocated, "referenced", &**self);
            }
        }
    }
}

// # This implementations has issues
// NOTE: This gets the inner value by replacing it with a default value and then putting the inner
// value back in
impl<T: HowMuchWhere + Default> HowMuchWhere for std::cell::Cell<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let inner = self.take();
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", &inner);
        self.set(inner);
    }
}

impl<T: StaticallyKnown + Default> StaticallyKnown for std::cell::Cell<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

// # This implementations has issues
// NOTE: This uses `borrow` to get the inner value with `try_borrow`, and will only report
// incomplete data if that fails
impl<T: HowMuchWhere> HowMuchWhere for std::cell::RefCell<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_const_size(
                "inline_overhead",
                mem::size_of::<Self>() - mem::size_of::<T>(),
                0,
            )
            .end_ref()
        });
        match self.try_borrow() {
            Ok(borrow) => collector.field(Inline, "wrapped", &*borrow).end_ref(),
            Err(_) => collector
                .field_const_size("wrapped_lower_bound", mem::size_of::<T>(), 0)
                .end_ref(),
        }
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::cell::RefCell<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

// # This implementations has issues
// NOTE: We *know* there's a value inside, as such we can return something, but only if the value
// memory usage is statically known
impl<T: StaticallyKnown> HowMuchWhere for std::cell::UnsafeCell<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::cell::UnsafeCell<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::cmp::Reverse<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", &self.0);
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::cmp::Reverse<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

// Most implementations use a `vec::IntoIter<OsString>` or are empty - the one exception is `sgx`,
// which I'm not going to support correctly here
fn collect_for_args<A: ExactSizeIterator>(args: &A, collector: &mut Collector) {
    use std::ffi::OsString;

    let mut collector = collector.collect_in_manual_struct::<A>();

    let capacity = std::env::args().len();

    collector.category("overhead", |c| {
        c.field_size_of_val(Inline, "inline_overhead", args)
            .field_const_size(
                "unused_capacity",
                0,
                (capacity - args.len()) * Layout::new::<OsString>().pad_to_align().size(),
            )
            .field_const_size(
                "data_padding",
                0,
                cumulative_padding::<OsString>(args.len()),
            )
            .end_ref()
    });

    for i in std::env::args_os().skip(capacity - args.len()) {
        collector.field(Allocated, "data", &i);
    }
}

impl HowMuchWhere for std::env::Args {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collect_for_args(self, collector);
    }
}

impl HowMuchWhere for std::env::ArgsOs {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collect_for_args(self, collector);
    }
}

impl HowMuchWhere for std::env::VarError {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::env::VarError;
        match *self {
            VarError::NotPresent => {
                collector.collect_in_variant::<Self>("NotPresent", None);
            }
            VarError::NotUnicode(ref data) => {
                collector
                    .collect_in_variant::<Self>("NotUnicode", None)
                    .field(Inline, "wrapped", data);
            }
        }
    }
}

impl HowMuchWhere for std::ffi::OsStr {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_size_of_val(Inline, "data", self);
    }
}

impl HowMuchWhere for std::ffi::OsString {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let actual_data_bytes = mem::size_of_val(self.as_os_str());
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .field_const_size(
                        "unused_capacity",
                        0,
                        (self.capacity() - self.len())
                            .checked_mul(actual_data_bytes)
                            .unwrap()
                            / self.len(),
                    )
                    .end_ref()
            })
            .field_const_size("data", 0, actual_data_bytes);
    }
}

impl HowMuchWhere for std::ffi::CStr {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("null_byte", 1, 0).end_ref()
            })
            .field_const_size("data", self.to_bytes().len(), 0);
    }
}

impl HowMuchWhere for std::ffi::CString {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .field_const_size("null_byte", 0, 1)
                    .end_ref()
            })
            .field_const_size("data", 0, self.as_bytes().len());
    }
}

impl HowMuchWhere for std::ffi::FromVecWithNulError {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Vec<u8>>(), 0)
                    .field_const_size("unused_capacity_unknown", 0, 1)
                    .end_ref()
            })
            .field_const_size(
                "inline_data",
                mem::size_of::<Self>().saturating_sub(mem::size_of::<Vec<u8>>()),
                0,
            )
            .field_const_size("data", 0, self.as_bytes().len());
    }
}

impl<R: HowMuchWhere> HowMuchWhere for std::io::BufReader<R> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<R>(),
                    0,
                )
                .field_const_size("buffer_used", 0, self.buffer().len())
                .field_const_size(
                    "buffer_capacity_unused",
                    0,
                    self.capacity() - self.buffer().len(),
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<W: HowMuchWhere + std::io::Write> HowMuchWhere for std::io::BufWriter<W> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<W>(),
                    0,
                )
                .field_const_size("buffer_used", 0, self.buffer().len())
                .field_const_size(
                    "buffer_capacity_unused",
                    0,
                    self.capacity() - self.buffer().len(),
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<T: HowMuchWhere, U: HowMuchWhere> HowMuchWhere for std::io::Chain<T, U> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let (left, right) = self.get_ref();
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "left", left)
            .field(Inline, "right", right);
    }
}

impl<T: StaticallyKnown, U: StaticallyKnown> StaticallyKnown for std::io::Chain<T, U> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<T>(Inline, "left")
            .field_statically_known::<U>(Inline, "right");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::io::Cursor<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::io::Cursor<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

/// # This implementation has issues
/// NOTE: This cannot look into dynamic errors besides the size of their main allocation.
impl HowMuchWhere for std::io::Error {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match self.get_ref() {
            None => {
                collector
                    .collect_in_variant::<Self>("Unboxed", None)
                    .field_const_size("value", 32 / 8, 0);
            }
            Some(inner) => {
                collector
                    .collect_in_manual_variant::<Self>("Boxed")
                    .category("overhead", |c| {
                        c.field_size_of_val(Inline, "inline_overhead", self)
                            .end_ref()
                    })
                    .field_size_of_val(Allocated, "error_base_alloc_size", inner);
            }
        }
    }
}

/// # This implementation has issues
/// NOTE: This requires `W` to be statically known because it cannot be accessed
impl<W: StaticallyKnown> HowMuchWhere for std::io::IntoInnerError<W> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<W>(Inline, "writer")
            .field(Inline, "error", self.error());
    }
}

impl<W: std::io::Write + HowMuchWhere> HowMuchWhere for std::io::LineWriter<W> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<W>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<T: std::io::Write + StaticallyKnown> StaticallyKnown for std::io::LineWriter<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::io::Take<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::io::Take<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

/// # This implementation has issues
/// NOTE: This requires `A` and `B` to be statically known because they cannot be accessed
impl<A: StaticallyKnown, B: StaticallyKnown> HowMuchWhere for std::iter::Chain<A, B> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector);
    }
}

impl<A: StaticallyKnown, B: StaticallyKnown> StaticallyKnown for std::iter::Chain<A, B> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<A>() - mem::size_of::<B>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<A>(Inline, "prefix")
            .field_statically_known::<B>(Inline, "suffix");
    }
}

/// # This implementation has issues
/// NOTE: This clones itself to access the data inside, which will however only provide a lower
/// bound for the actual memory consumption (or a completely incorrect one depending on the kinds
/// of types inside)
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::iter::Once<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match self.clone().next() {
            None => {
                collector.collect_in_variant::<Self>("Exhausted", None);
            }
            Some(val) => {
                collector
                    .collect_in_variant::<Self>("Filled", None)
                    .field(Inline, "item", &val);
            }
        }
    }
}

/// # This implementation has issues
/// NOTE: This clones itself to access the data inside, which will however only provide a lower
/// bound for the actual memory consumption (or a completely incorrect one depending on the kinds
/// of types inside)
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::iter::Repeat<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "item", &self.clone().next().unwrap());
    }
}

impl<T: StaticallyKnown + Clone> StaticallyKnown for std::iter::Repeat<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<T>(Inline, "item");
    }
}

/// # This implementation has issues
/// NOTE: This requires `A` and `B` to be statically known because they cannot be accessed
impl<A: StaticallyKnown, B: StaticallyKnown> HowMuchWhere for std::iter::Zip<A, B> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector);
    }
}

impl<A: StaticallyKnown, B: StaticallyKnown> StaticallyKnown for std::iter::Zip<A, B> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<A>() - mem::size_of::<B>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<A>(Inline, "left")
            .field_statically_known::<B>(Inline, "right");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::num::Wrapping<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", &self.0);
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::num::Wrapping<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<Idx: HowMuchWhere> HowMuchWhere for std::ops::Range<Idx> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "start", &self.start)
            .field(Inline, "end", &self.end);
    }
}

impl<Idx: StaticallyKnown> StaticallyKnown for std::ops::Range<Idx> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<Idx>(Inline, "start")
            .field_statically_known::<Idx>(Inline, "end");
    }
}

impl<Idx: HowMuchWhere> HowMuchWhere for std::ops::RangeFrom<Idx> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "start", &self.start);
    }
}

impl<Idx: StaticallyKnown> StaticallyKnown for std::ops::RangeFrom<Idx> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<Idx>(Inline, "start");
    }
}

impl<Idx: HowMuchWhere> HowMuchWhere for std::ops::RangeInclusive<Idx> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "start", self.start())
            .field(Inline, "end", self.end());
    }
}

impl<Idx: StaticallyKnown> StaticallyKnown for std::ops::RangeInclusive<Idx> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<Idx>(Inline, "start")
            .field_statically_known::<Idx>(Inline, "end");
    }
}

impl<Idx: HowMuchWhere> HowMuchWhere for std::ops::RangeTo<Idx> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "end", &self.end);
    }
}

impl<Idx: StaticallyKnown> StaticallyKnown for std::ops::RangeTo<Idx> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<Idx>(Inline, "end");
    }
}

impl<Idx: HowMuchWhere> HowMuchWhere for std::ops::RangeToInclusive<Idx> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "end", &self.end);
    }
}

impl<Idx: StaticallyKnown> StaticallyKnown for std::ops::RangeToInclusive<Idx> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<Idx>(Inline, "end");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::ops::Bound<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::ops::Bound;

        match *self {
            Bound::Included(ref x) => {
                collector
                    .collect_in_variant::<Self>("Included", None)
                    .field(Inline, "wrapped", x);
            }
            Bound::Excluded(ref x) => {
                collector
                    .collect_in_variant::<Self>("Excluded", None)
                    .field(Inline, "wrapped", x);
            }
            Bound::Unbounded => {
                collector.collect_in_variant::<Self>("Unbounded", None);
            }
        }
    }
}

impl<B: HowMuchWhere, C: HowMuchWhere> HowMuchWhere for std::ops::ControlFlow<B, C> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::ops::ControlFlow;

        match *self {
            ControlFlow::Continue(ref x) => {
                collector
                    .collect_in_variant::<Self>("Included", None)
                    .field(Inline, "wrapped", x);
            }
            ControlFlow::Break(ref x) => {
                collector
                    .collect_in_variant::<Self>("Break", None)
                    .field(Inline, "wrapped", x);
            }
        }
    }
}

/// # This implementation has issues
/// NOTE: This clones itself to access the data inside, which will however only provide a lower
/// bound for the actual memory consumption (or a completely incorrect one depending on the kinds
/// of types inside)
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::option::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match self.clone().next() {
            None => {
                collector.collect_in_variant::<Self>("ExhaustedOrNone", None);
            }
            Some(val) => {
                collector
                    .collect_in_variant::<Self>("Some", None)
                    .field(Inline, "item", &val);
            }
        }
    }
}

impl<T: HowMuchWhere> HowMuchWhere for Option<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match *self {
            None => {
                collector.collect_in_variant::<Self>("None", None);
            }
            Some(ref val) => {
                collector
                    .collect_in_variant::<Self>("Some", None)
                    .field(Inline, "wrapped", val);
            }
        }
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::panic::AssertUnwindSafe<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", &self.0);
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::panic::AssertUnwindSafe<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl HowMuchWhere for std::path::Path {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_unsized_struct(self)
            .field_size_of_val(Inline, "data", self);
    }
}

impl HowMuchWhere for std::path::PathBuf {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let actual_data_bytes = mem::size_of_val(self.as_os_str());
        let len = self.as_os_str().len();
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .field_const_size(
                        "unused_capacity",
                        0,
                        (self.capacity() - len)
                            .checked_mul(actual_data_bytes)
                            .unwrap()
                            / len,
                    )
                    .end_ref()
            })
            .field_const_size("data", 0, actual_data_bytes);
    }
}

/// # This implementation has issues
/// NOTE: This cannot get a "normal" reference into the inner data, but *can* get a reference to
/// whatever is being pointed to, so it just assumes the inner pointer doesn't have an allocated
/// overhead and counts the inline overhead as its own.
impl<T: std::ops::Deref<Target = D>, D: HowMuchWhere> HowMuchWhere for std::pin::Pin<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Self>(), 0)
                    .end_ref()
            })
            .field(Shared, "wrapped", self.as_ref().get_ref()); // It might *not* be shared, but we can't know
    }
}

impl HowMuchWhere for std::process::Command {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::collections::BTreeMap;
        use std::ffi::OsString;

        type Env = BTreeMap<OsString, Option<OsString>>;

        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector
            .field_const_size(
                "inline_data",
                mem::size_of::<Self>() - mem::size_of::<Env>(),
                0,
            )
            .field(Allocated, "program", self.get_program());

        for i in self.get_args() {
            collector.field(Allocated, "args", i);
        }

        if let Some(current_dir) = self.get_current_dir() {
            collector.field(Allocated, "current_dir", current_dir);
        }

        collector.ignore_size_chunk(mem::size_of::<Env>());
        collector.field_generic("envs", None, |c| {
            let mut c = c.collect_in_manual_struct::<Env>();

            c.category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Env>(), 0)
                    .end_ref()
            });

            let mut size = 0;
            for (k, v) in self.get_envs() {
                // This is *technically* not correct sinec we're putting `OsStr`s here, but
                // they're close enough - plus we don't have access to the `OsString`s either
                // way
                c.field(Allocated, "keys", k);
                c.field_generic(
                    // why oh why
                    "values",
                    None,
                    |c| match v {
                        None => {
                            c.collect_in_variant::<Option<OsString>>("None", None);
                        }
                        Some(val) => {
                            c.collect_in_variant::<Option<OsString>>("Some", None)
                                .field(Inline, "wrapped", val);
                        }
                    },
                );
                size += 1;
            }

            apply_btree_info::<OsString, Option<OsString>>(size, &mut c);
        });
    }
}

impl HowMuchWhere for std::process::Output {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field(Inline, "status", &self.status)
            .field(Inline, "stdout", &self.stdout)
            .field(Inline, "stderr", &self.stderr);
    }
}

struct RcBox<'a, T>(&'a T);

impl<'a, T: HowMuchWhere> HowMuchWhere for RcBox<'a, T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        struct RcBoxLayout<T> {
            _strong: usize,
            _weak: usize,
            _value: T,
        }

        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "alloc_overhead",
                    mem::size_of::<RcBoxLayout<T>>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "referenced", self.0);
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::rc::Rc<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .end_ref()
            })
            .shared_field_via("alloc", &**self, &RcBox(&**self));
    }
}

/// # This implementation has issues
/// NOTE: This relies on cloning itself to access the internal data, which means referenced data
/// that gets reallocated might have a different size, additionally the capacity is unknown
impl<T: HowMuchWhere + Clone> HowMuchWhere for std::result::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match self.clone().next() {
            None => {
                collector.collect_in_variant::<Self>("ExhaustedOrErr", None);
            }
            Some(val) => {
                collector
                    .collect_in_variant::<Self>("Ok", None)
                    .field(Inline, "item", &val);
            }
        }
    }
}

impl<T: HowMuchWhere, E: HowMuchWhere> HowMuchWhere for Result<T, E> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        match *self {
            Ok(ref val) => {
                collector
                    .collect_in_variant::<Self>("Ok", None)
                    .field(Inline, "wrapped", val);
            }
            Err(ref val) => {
                collector
                    .collect_in_variant::<Self>("Err", None)
                    .field(Inline, "wrapped", val);
            }
        }
    }
}

/// # This implementation has issues
/// NOTE: Sadly it's impossible to retrieve the capacity
impl HowMuchWhere for std::string::FromUtf8Error {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Vec<u8>>(), 0)
                    .end_ref()
            })
            .field(Allocated, "bytes", self.as_bytes())
            .field(Inline, "error", &self.utf8_error());
    }
}

impl HowMuchWhere for str {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_unsized_struct(self)
            .field_size_of_val(Inline, "data", self);
    }
}

impl HowMuchWhere for String {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .field_const_size("unused_capacity", 0, self.capacity() - self.len())
                    .end_ref()
            })
            .field(Allocated, "wrapped", &**self);
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::sync::mpsc::SendError<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", &self.0);
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::sync::mpsc::SendError<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::sync::mpsc::TrySendError<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::sync::mpsc::TrySendError;

        match *self {
            TrySendError::Full(ref val) => collector
                .collect_in_variant::<Self>("Full", None)
                .field(Inline, "wrapped", val)
                .end_ref(),
            TrySendError::Disconnected(ref val) => collector
                .collect_in_variant::<Self>("Disconnected", None)
                .field(Inline, "wrapped", val)
                .end_ref(),
        }
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::sync::Arc<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_size_of_val(Inline, "inline_overhead", self)
                    .end_ref()
            })
            .shared_field_via("alloc", &**self, &RcBox(&**self));
    }
}

impl HowMuchWhere for std::sync::Barrier {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_size_of_val(Inline, "inline_data", self)
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

impl StaticallyKnown for std::sync::Barrier {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_const_size("inline_data", mem::size_of::<Self>(), 0)
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

impl HowMuchWhere for std::sync::Condvar {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_size_of_val(Inline, "inline_data", self)
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

impl StaticallyKnown for std::sync::Condvar {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .field_const_size("inline_data", mem::size_of::<Self>(), 0)
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

// # This implementation has issues
// NOTE: This tries to lock itself to figure out what's inside, if it can't without blocking it
// will not count the data inside correctly.
impl<T: HowMuchWhere> HowMuchWhere for std::sync::Mutex<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::sync::TryLockError;

        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_const_size(
                "inline_overhead",
                mem::size_of::<Self>() - mem::size_of::<T>(),
                0,
            )
            .field_const_size("alloc_overhead_unknown", 0, 1)
            .end_ref()
        });

        match self.try_lock() {
            Ok(value) => collector
                .field_size_of_val(Inline, "wrapped", &*value)
                .end_ref(),
            res @ Err(TryLockError::Poisoned(_)) => mem::drop(res.unwrap()), // We just want to generate the correct panic
            Err(TryLockError::WouldBlock) => collector
                .field_const_size("data_lower_bound", mem::size_of::<T>(), 0)
                .end_ref(),
        }
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::sync::Mutex<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .field_const_size("alloc_overhead_unknown", 0, 1)
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::sync::PoisonError<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field(Inline, "wrapped", self.get_ref());
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::sync::PoisonError<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

// # This implementation has issues
// NOTE: This tries to lock itself to figure out what's inside, if it can't without blocking it
// will not count the data inside correctly.
impl<T: HowMuchWhere> HowMuchWhere for std::sync::RwLock<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::sync::TryLockError;

        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_const_size(
                "inline_overhead",
                mem::size_of::<Self>() - mem::size_of::<T>(),
                0,
            )
            .field_const_size("alloc_overhead_unknown", 0, 1)
            .end_ref()
        });

        match self.try_read() {
            Ok(value) => collector
                .field_size_of_val(Inline, "wrapped", &*value)
                .end_ref(),
            res @ Err(TryLockError::Poisoned(_)) => mem::drop(res.unwrap()), // We just want to generate the correct panic
            Err(TryLockError::WouldBlock) => collector
                .field_const_size("data_lower_bound", mem::size_of::<T>(), 0)
                .end_ref(),
        }
    }
}

impl<T: StaticallyKnown> StaticallyKnown for std::sync::RwLock<T> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size(
                    "inline_overhead",
                    mem::size_of::<Self>() - mem::size_of::<T>(),
                    0,
                )
                .field_const_size("alloc_overhead_unknown", 0, 1)
                .end_ref()
            })
            .field_statically_known::<T>(Inline, "wrapped");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::sync::TryLockError<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::sync::TryLockError;

        match *self {
            TryLockError::Poisoned(ref p) => collector
                .collect_in_variant::<Self>("Poisoned", None)
                .field(Inline, "wrapped", p)
                .end_ref(),
            TryLockError::WouldBlock => collector
                .collect_in_variant::<Self>("WouldBlock", None)
                .end_ref(),
        }
    }
}

impl HowMuchWhere for std::task::RawWaker {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector)
    }
}

impl StaticallyKnown for std::task::RawWaker {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Self>(), 0)
                    .end_ref()
            })
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

impl HowMuchWhere for std::task::Waker {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector)
    }
}

impl StaticallyKnown for std::task::Waker {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_manual_struct::<Self>()
            .category("overhead", |c| {
                c.field_const_size("inline_overhead", mem::size_of::<Self>(), 0)
                    .end_ref()
            })
            .field_const_size("alloc_data_unknown", 0, 1);
    }
}

impl<T: HowMuchWhere> HowMuchWhere for std::task::Poll<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        use std::task::Poll;

        match *self {
            Poll::Ready(ref val) => {
                collector
                    .collect_in_variant::<Self>("Ready", None)
                    .field(Inline, "wrapped", &val);
            }
            Poll::Pending => {
                collector.collect_in_variant::<Self>("Pending", None);
            }
        }
    }
}

macro_rules! static_size_alloc_unknown {
    {$({$($implpre:tt)*} {$($implpost:tt)*})*} => {
        $(
            $($implpre)* HowMuchWhere $($implpost)* {
                fn how_much_where_impl(&self, collector: &mut Collector) {
                    Self::how_much_where_impl_static(collector);
                }
            }

            $($implpre)* StaticallyKnown $($implpost)* {
                fn how_much_where_impl_static(collector: &mut Collector) {
                    collector.collect_in_manual_struct::<Self>()
                        .field_const_size("inline_data", mem::size_of::<Self>(), 0)
                        .field_const_size("alloc_data_unknown", 0, 1);
                }
            }
        )*
    }
}

static_size_alloc_unknown! {
    {impl} {for std::thread::Builder}
    {impl<T>} {for std::thread::JoinHandle<T>}
    {impl<'scope, T>} {for std::thread::ScopedJoinHandle<'scope, T>}
    {impl} {for std::thread::Thread}
}

/// # This implementation has issues
/// NOTE: Sadly it's impossible to retrieve the capacity of `IntoIter`
impl<T: HowMuchWhere> HowMuchWhere for std::vec::IntoIter<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        let mut collector = collector.collect_in_manual_struct::<Self>();
        collector.category("overhead", |c| {
            c.field_size_of_val(Inline, "inline_overhead", self)
                .field_const_size("unused_capacity_unknown", 0, 1)
                .end_ref()
        });

        // Sadly we can't access the data without cloning
        let mut len = 0usize;
        for i in self.as_slice() {
            collector.field(Allocated, "data", i);
            len += 1;
        }

        collector.category("overhead", |c| {
            c.field_const_size("data_padding", 0, cumulative_padding::<T>(len))
                .end_ref()
        });
    }
}

/// # This implementation has issues
/// NOTE: This requires `I` to be statically known because it cannot be accessed
impl<'a, I: Iterator + StaticallyKnown + 'a> HowMuchWhere for std::vec::Splice<'a, I> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        Self::how_much_where_impl_static(collector);
    }
}

impl<'a, I: Iterator + StaticallyKnown + 'a> StaticallyKnown for std::vec::Splice<'a, I> {
    fn how_much_where_impl_static(collector: &mut Collector) {
        collector
            .collect_in_struct::<Self>()
            .field_statically_known::<std::vec::Drain<'a, I::Item>>(Inline, "drain")
            .field_statically_known::<I>(Inline, "replace_with");
    }
}

impl<T: HowMuchWhere> HowMuchWhere for Vec<T> {
    fn how_much_where_impl(&self, collector: &mut Collector) {
        veclike_collection(self, self.len(), self.capacity(), collector);
    }
}

macro_rules! impl_for_fn {
    {@cont $firstarg:ident $($args:ident)*} => {
        impl_for_fn!{$($args)*}
    };
    {@cont} => {};
    {$($args:ident)*} => {
        impl<$($args: ?Sized,)* R: ?Sized> HowMuchWhere for fn($($args),*) -> R {
            fn how_much_where_impl(&self, collector: &mut Collector) {
                Self::how_much_where_impl_static(collector)
            }
        }

        impl<$($args: ?Sized,)* R: ?Sized> StaticallyKnown for fn($($args),*) -> R {
            fn how_much_where_impl_static(collector: &mut Collector) {
                collector.collect_in_manual_struct::<Self>()
                    .field_const_size("value", mem::size_of::<Self>(), 0);
            }
        }

        impl_for_fn!{@cont $($args)*}
    }
}

impl_for_fn! {A B C D E F G H I J K L M N O P}

macro_rules! impl_for_tuple {
    {
        @cont
            $firstarg:ident $firstname:literal $firstaccess:tt
            $($args:ident $names:literal $accesses:tt)*
    } => {
        impl_for_tuple!{$($args $names $accesses)*}
    };
    {@cont} => {};
    (@makety ($($out:tt)*) $next:tt $($rest:tt)*) => {
        impl_for_tuple!(@makety ($next, $($out)*) $($rest)*)
    };
    (@makety ($($out:tt)*)) => {
        ($($out)*)
    };
    {$($args:ident $names:literal $accesses:tt)*} => {
        impl<$($args: HowMuchWhere),*> HowMuchWhere for impl_for_tuple!(@makety () $($args)*) {
            fn how_much_where_impl(&self, collector: &mut Collector) {
                collector.collect_in_struct::<Self>()
                    $(
                        .field(Inline, $names, &self.$accesses)
                    )*;
            }
        }

        impl<$($args: StaticallyKnown),*> StaticallyKnown for impl_for_tuple!(@makety () $($args)*) {
            fn how_much_where_impl_static(collector: &mut Collector) {
                collector.collect_in_struct::<Self>()
                    // NOTE: This is ordered in reverse, just as the inputs, but thanks to the type
                    // having been put in reverse above, the first type in here will be both the
                    // last type in the tuple and the last input, which contains the first name.
                    $(
                        .field_statically_known::<$args>(Inline, $names)
                    )*;
            }
        }

        impl_for_tuple!{@cont $($args $names $accesses)*}
    }
}

// NOTE: This has to be in reverse because the recursion to do the next, smaller tuple removes the
// *first* thing in the invocation, as there is no (sane) way to remove the last.
impl_for_tuple! {
    P "15" 15 O "14" 14 N "13" 13 M "12" 12 L "11" 11 K "10" 10 J "9" 9 I "8" 8
    H "7" 7 G "6" 6 F "5" 5 E "4" 4 D "3" 3 C "2" 2
    B "snd" 1 A "fst" 0
}

macro_rules! how_much_where_by_size_of {
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident ::
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{@read ($($outer_prefix)*) ($($prefix)* $name::) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            { $($inner:tt)* }
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{@read ($($prefix)*) ($($prefix)*) $($inner)*}
        how_much_where_by_size_of!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?),* $(,)?
                $($gty:ident $(: ($($gtybounds:tt)*))?),* $(,)?
                $(; const $gconst:ident: $gconstty:ty)*
            >
            where {$($where:tt)*}
            $($rest:tt)*
    } => {
        opaque_wrapper!{
            @type
                $($prefix)* $name<
                    $($glt $(: $glt2f $(+ $glt2)*)?,)*
                    $($gty $(: ($($gtybounds)*))?,)*
                    $(; const $gconst: $gconstty)*
                >
                where $($where)*
        }
        opaque_wrapper!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?),* $(,)?
                $($gty:ident $(: ($($gtybounds:tt)*))?),* $(,)?
                $(; const $gconst:ident: $gconstty:ty)*
            >
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{
            @type
                $($prefix)* $name<
                    $($glt $(: $glt2f $(+ $glt2)*)?,)*
                    $($gty $(: ($($gtybounds)*))?,)*
                    $(; const $gconst: $gconstty)*
                >
        }
        how_much_where_by_size_of!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident where {$($where:tt)*}
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{@type $($prefix)* $name where $($where)*}
        how_much_where_by_size_of!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{@type $($prefix)* $name}
        how_much_where_by_size_of!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)+)
    } => {};
    {
        @cont ($($prefix:tt)*)
            ,
            $($rest:tt)*
    } => {
        how_much_where_by_size_of!{@read ($($prefix)*) ($($prefix)*) $($rest)*}
    };
    {
        @cont ($($prefix:tt)*)
    } => {};
    {
        @type
            $moduleorty:ident $(:: $moduleortyext:ident)* $(<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?,)*
                $($gty:ident $(: ($($gtybounds:tt)*))?,)*
                $(; const $gconst:ident: $gconstty:ty)*
            >)?
            $(where $($where:tt)*)?
    } => {
        impl $(<
            $($glt $(: $glt2f $(+ $glt2)*)?,)*
            $($gty $(: $($gtybounds)*)?,)*
            $(const $gconst: $gconstty,)*
        >)?
        $crate::HowMuchWhere
        for $moduleorty $(:: $moduleortyext)* $(<
            $($glt,)*
            $($gty,)*
            $($gconst,)*
        >)?
        $(where $($where)*)?
        {
            fn how_much_where_impl(&self, collector: &mut $crate::Collector) {
                Self::how_much_where_impl_static(collector);
            }
        }

        impl $(<
            $($glt $(: $glt2f $(+ $glt2)*)?,)*
            $($gty $(: $($gtybounds)*)?,)*
            $(const $gconst: $gconstty,)*
        >)?
        $crate::StaticallyKnown
        for $moduleorty $(:: $moduleortyext)* $(<
            $($glt,)*
            $($gty,)*
            $($gconst,)*
        >)?
        $(where $($where)*)?
        {
            fn how_much_where_impl_static(collector: &mut $crate::Collector) {
                collector.collect_in_manual_struct::<Self>()
                    .field_const_size("value", mem::size_of::<Self>(), 0);
            }
        }
    };
    // with an initial ident to make debugigng easier in case of otherwise infinite macro recursion
    {$initial:ident $($rest:tt)*} => {
        how_much_where_by_size_of!{@read () () $initial $($rest)*}
    };
}

how_much_where_by_size_of! {
    bool, char, f32, f64, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize,
    std::{
        alloc::{Layout, LayoutError, System}, any::TypeId,
        array::{IntoIter<T; const N: usize>, TryFromSliceError}, ascii::EscapeDefault,
        char::{
            CharTryFromError, DecodeUtf16<T: (Iterator<Item = u16>)>, DecodeUtf16Error, EscapeDebug,
            EscapeDefault, EscapeUnicode, ParseCharError, ToLowercase, ToUppercase, TryFromCharError
        },
        cmp::Ordering,
        collections::{
            binary_heap::{Drain<'a, T: ('a)>, Iter<'a, T: ('a)>, PeekMut<'a, T: (Ord + 'a)>},
            btree_map::{
                Iter<'a, K: ('a), V: ('a)>, IterMut<'a, K: ('a), V: ('a)>,
                Keys<'a, K: ('a), V: ('a)>, OccupiedEntry<'a, K: ('a), V: ('a)>,
                RangeMut<'a, K: ('a), V: ('a)>, Range<'a, K: ('a), V: ('a)>,
                VacantEntry<'a, K: ('a), V: ('a)>, Values<'a, K: ('a), V: ('a)>,
                ValuesMut<'a, K: ('a), V: ('a)>, Entry<'a, K: ('a), V: ('a)>
            },
            btree_set::{
                Difference<'a, T: ('a)>, Intersection<'a, T: ('a)>, Range<'a, T: ('a)>,
                Iter<'a, T: ('a)>, SymmetricDifference<'a, T: ('a)>, Union<'a, T: ('a)>
            },
            hash_map::{
                DefaultHasher, Drain<'a, K: ('a), V: ('a)>, Iter<'a, K: ('a), V: ('a)>,
                IterMut<'a, K: ('a), V: ('a)>, Keys<'a, K: ('a), V: ('a)>,
                OccupiedEntry<'a, K: ('a), V: ('a)>, RandomState,
                VacantEntry<'a, K: ('a), V: ('a)>, Values<'a, K: ('a), V: ('a)>,
                ValuesMut<'a, K: ('a), V: ('a)>,
            },
            hash_set::{
                Difference<'a, T: ('a), S: ('a)>, Drain<'a, T: ('a)>,
                Intersection<'a, T: ('a), S: ('a)>, Iter<'a, T: ('a)>,
                SymmetricDifference<'a, T: ('a), S: ('a)>, Union<'a, T: ('a), S: ('a)>,
            },
            linked_list::{Iter<'a, T: ('a)>, IterMut<'a, T: ('a)>},
            vec_deque::{Drain<'a, T: ('a)>, Iter<'a, T: ('a)>, IterMut<'a, T: ('a)>},
            TryReserveError
        },
        convert::Infallible, env::{JoinPathsError, SplitPaths<'a>},
        ffi::{c_void, FromBytesWithNulError},
        fmt::{
            Arguments<'a>, DebugList<'a, 'b: 'a>, DebugMap<'a, 'b: 'a>, DebugSet<'a, 'b: 'a>,
            DebugStruct<'a, 'b: 'a>, DebugTuple<'a, 'b: 'a>, Error, Formatter<'a>, Alignment
        },
        fs::{DirBuilder, DirEntry, File, FileType, Metadata, OpenOptions, Permissions, ReadDir},
        future::{Pending<T>, Ready<T>}, hash::BuildHasherDefault<H>,
        io::{
            Empty, IoSlice<'a>, IoSliceMut<'a>, Sink, Repeat, Stderr, StderrLock<'a>, Stdin,
            StdinLock<'a>, Stdout, StdoutLock<'a>, ErrorKind, SeekFrom
        },
        iter::Empty<T>, marker::{PhantomData<T: (?Sized)>, PhantomPinned},
        mem::{Discriminant<T>, ManuallyDrop<T>},
        net::{
            AddrParseError, Incoming<'a>, Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6,
            TcpListener, TcpStream, UdpSocket, IpAddr, Shutdown, SocketAddr
        },
        num::{
            NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize,
            NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
            ParseFloatError, ParseIntError, TryFromIntError, FpCategory, IntErrorKind
        },
        ops::RangeFull, option::{Iter<'a, T: ('a)>, IterMut<'a, T: ('a)>},
        panic::{Location<'a>, PanicInfo<'a>},
        path::{
            Ancestors<'a>, Components<'a>, Display<'a>, Iter<'a>, PrefixComponent<'a>,
            StripPrefixError, Component<'a>, Prefix<'a>
        },
        process::{
            Child, ChildStderr, ChildStdin, ChildStdout, CommandArgs<'a>, CommandEnvs<'a>, ExitCode,
            ExitStatus, Stdio
        },
        rc::Weak<T: (?Sized)>, result::{Iter<'a, T: ('a)>, IterMut<'a, T: ('a)>}
    }
}

how_much_where_by_size_of! {
    std::{
        slice::{
            Chunks<'a, T: ('a)>, ChunksExact<'a, T: ('a)>, ChunksExactMut<'a, T: ('a)>,
            ChunksMut<'a, T: ('a)>, EscapeAscii<'a>, Iter<'a, T: ('a)>, IterMut<'a, T: ('a)>,
            RChunks<'a, T: ('a)>, RChunksExact<'a, T: ('a)>, RChunksExactMut<'a, T: ('a)>,
            RChunksMut<'a, T: ('a)>,
            RSplit<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            RSplitMut<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            RSplitN<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            RSplitNMut<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            Split<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            SplitInclusive<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            SplitInclusiveMut<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            SplitMut<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            SplitN<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            SplitNMut<'a, T: ('a), P: (FnMut(&T) -> bool)>,
            Windows<'a, T: ('a)>
        },
        str::{
            Bytes<'a>, CharIndices<'a>, Chars<'a>, EncodeUtf16<'a>, EscapeDebug<'a>,
            EscapeDefault<'a>, EscapeUnicode<'a>, Lines<'a>,
            ParseBoolError,
            SplitAsciiWhitespace<'a>,
            SplitWhitespace<'a>,
            Utf8Error
        },
        string::{Drain<'a>, FromUtf16Error},
        sync::{
            atomic::{
                AtomicBool,
                AtomicI8, AtomicI16, AtomicI32, AtomicI64, AtomicIsize,
                AtomicU8, AtomicU16, AtomicU32, AtomicU64, AtomicUsize,
                Ordering
            },
            mpsc::{
                Iter<'a, T: ('a)>, RecvError, TryIter<'a, T: ('a)>, RecvTimeoutError, TryRecvError
            },
            BarrierWaitResult, MutexGuard<'a, T: (?Sized + 'a)>,
            // technically `Once` *might* currently have a waiter attached, but it usually won't,
            // and we can't check for that anyway
            Once, OnceState,
            RwLockReadGuard<'a, T: (?Sized + 'a)>, RwLockWriteGuard<'a, T: (?Sized + 'a)>,
            WaitTimeoutResult, Weak<T: (?Sized)>
        },
        task::{Context<'a>, RawWakerVTable},
        thread::{AccessError, LocalKey<T: ('static)>, ThreadId},
        time::{Duration, Instant, SystemTime, SystemTimeError}, vec::Drain<'a, T: ('a)>
    }
}

// adapted from `how_much_where_by_size_of!`
macro_rules! opaque_wrapper {
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident ::
            $($rest:tt)*
    } => {
        opaque_wrapper!{@read ($($outer_prefix)*) ($($prefix)* $name::) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            { $($inner:tt)* }
            $($rest:tt)*
    } => {
        opaque_wrapper!{@read ($($prefix)*) ($($prefix)*) $($inner)*}
        opaque_wrapper!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?),* $(,)?
                $gty:ident $(: ($($gtybounds:tt)*))? $(,)?
                $(; const $gconst:ident: $gconstty:ty)*
            >
            where {$($where:tt)*}
            $($rest:tt)*
    } => {
        opaque_wrapper!{
            @type
                $($prefix)* $name<
                    $($glt $(: $glt2f $(+ $glt2)*)?,)*
                    $gty $(: ($($gtybounds)*))?
                    $(; const $gconst: $gconstty)*
                >
                where $($where)*
        }
        opaque_wrapper!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)*)
            $name:ident<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?),* $(,)?
                $gty:ident $(: ($($gtybounds:tt)*))? $(,)?
                $(; const $gconst:ident: $gconstty:ty)*
            >
            $($rest:tt)*
    } => {
        opaque_wrapper!{
            @type
                $($prefix)* $name<
                    $($glt $(: $glt2f $(+ $glt2)*)?,)*
                    $gty $(: ($($gtybounds)*))?
                    $(; const $gconst: $gconstty)*
                >
        }
        opaque_wrapper!{@cont ($($outer_prefix)*) $($rest)*}
    };
    {
        @read ($($outer_prefix:tt)*) ($($prefix:tt)+)
    } => {};
    {
        @cont ($($prefix:tt)*)
            ,
            $($rest:tt)*
    } => {
        opaque_wrapper!{@read ($($prefix)*) ($($prefix)*) $($rest)*}
    };
    {
        @cont ($($prefix:tt)*)
    } => {};
    {
        @type
            $moduleorty:ident $(:: $moduleortyext:ident)*<
                $($glt:lifetime $(: $glt2f:lifetime $(+ $glt2:lifetime)*)?,)*
                $gty:ident $(: ($($gtybounds:tt)*))?
                $(; const $gconst:ident: $gconstty:ty)*
            >
            $(where $($where:tt)*)?
    } => {
        impl<
            $($glt $(: $glt2f $(+ $glt2)*)?,)*
            $gty : StaticallyKnown $(+ $($gtybounds)*)?
            $(, const $gconst: $gconstty,)*
        >
        $crate::HowMuchWhere
        for $moduleorty $(:: $moduleortyext)*<
            $($glt,)*
            $gty
            $(, $gconst)*
        >
        $(where $($where)*)?
        {
            fn how_much_where_impl(&self, collector: &mut $crate::Collector) {
                Self::how_much_where_impl_static(collector);
            }
        }

        impl<
            $($glt $(: $glt2f $(+ $glt2)*)?,)*
            $gty : StaticallyKnown $(+ $($gtybounds)*)?
            $(, const $gconst: $gconstty,)*
        >
        $crate::StaticallyKnown
        for $moduleorty $(:: $moduleortyext)*<
            $($glt,)*
            $gty
            $(, $gconst,)*
        >
        $(where $($where)*)?
        {
            fn how_much_where_impl_static(collector: &mut $crate::Collector) {
                collector.collect_in_manual_struct::<Self>()
                    .category(
                        "overhead",
                        |c| c
                            .field_const_size("inline_overhead", mem::size_of::<Self>() - mem::size_of::<$gty>(), 0)
                            .end_ref()
                    )
                    .field_statically_known::<$gty>(Inline, "wrapped");
            }
        }
    };
    // with an initial ident to make debugigng easier in case of otherwise infinite macro recursion
    {$initial:ident $($rest:tt)*} => {
        opaque_wrapper!{@read () () $initial $($rest)*}
    };
}

opaque_wrapper! {
    std::{
        io::{Bytes<R>, Lines<R>, Split<B>},
        iter::{
            Cloned<I>, Copied<I>, Cycle<I>, Enumerate<I>,
            Flatten<I: (Iterator)> where {<I as Iterator>::Item: Iterator},
            Fuse<I>, Peekable<I: (Iterator)>, Rev<I>, Skip<I>, StepBy<I>, Take<I>
        }
    }
}

// TODO: Document
// Cannot be implemented for:
// * std::collections::btree_map::IntoIter
// * std::collections::btree_map::IntoKeys
// * std::collections::btree_map::IntoValues
// * std::collections::btree_set::IntoIter
// * std::collections::hash_map::IntoIter
// * std::collections::hash_map::IntoKeys
// * std::collections::hash_map::IntoValues
// * std::collections::hash_set::IntoIter
// * std::ffi::IntoStringError
// * std::ffi::NulError
// * std::io::WriterPanicked
// * std::iter::Filter
// * std::iter::FilterMap
// * std::iter::FlatMap
// * std::iter::FromFn
// * std::iter::Inspect
// * std::iter::Map
// * std::iter::MapWhile
// * std::iter::OnceWith
// * std::iter::RepeatWith
// * std::iter::Scan
// * std::iter::SkipWhile
// * std::iter::Successors
// * std::iter::TakeWhile
// * std::mem::MaybeUninit
// * std::ptr::NonNull
// * std::sync::atomic::AtomicPtr
// * std::sync::mpsc::IntoIter
// * std::sync::mpsc::Receiver
// * std::sync::mpsc::Sender
// * std::sync::mpsc::SyncSender
//
// Would require nightly due to traits on arguments:
// * std::str::MatchIndices
// * std::str::Matches
// * std::str::RMatchIndices
// * std::str::RMatches
// * std::str::RSplit
// * std::str::RSplitN
// * std::str::RSplitTerminator
// * std::str::Split
// * std::str::SplitInclusive
// * std::str::SplitN
// * std::str::SplitTerminator
//
// Cannot be reasonably implemented for in regards to capacity vs contained:
// * std::env::Vars
// * std::env::VarsOs
//
// untouched:
// * anything nightly
// * `std::arch`
// * `std::os`
//
// TODO: Maybe StaticallyKnown for ZSTs?
//
// TODO: Deduplicate some stuff with macros
