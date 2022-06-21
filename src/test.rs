use super::*;
use std::os::raw::c_int;

macro_rules! path {
    [@impl : ($t:ty)] => {
        (Kind::Type, std::any::type_name::<$t>())
    };
    [@impl : $t:ty] => {
        (Kind::Type, std::any::type_name::<$t>())
    };
    [@impl / $t:ident] => {
        (Kind::Variant, stringify!($t))
    };
    [@impl + $t:ident] => {
        (Kind::Category, stringify!($t))
    };
    [@impl . $t:ident] => {
        (Kind::Field, stringify!($t))
    };
    [$($k:tt $x:tt)*] => {
        vec![$(path![@impl $k $x]),*]
    };
}

macro_rules! hash_map {
    {$($key:expr => $val:expr),* $(,)?} => {{
        let mut out = HashMap::new();
        $(
            out.insert($key, $val);
        )*
        out
    }}
}

const PTR_SIZE: usize = mem::size_of::<usize>();

#[test]
fn test_primitive() {
    assert_eq!(
        (3u16).how_much_where(),
        CollectionResult {
            root: hash_map!{ path![:u16.value] => 2 },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_vec_of_primitive() {
    let mut vec = Vec::with_capacity(4);
    vec.push(0u16);
    vec.push(42u16);
    assert_eq!(
        vec.how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:(Vec<u16>)+overhead.inline_overhead] => mem::size_of::<Vec<u16>>(),
                path![:(Vec<u16>)+overhead.unused_capacity] => 2 * 2,
                path![:(Vec<u16>).data:u16.value] => 2 * 2,
            },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_derive_fieldless_enum() {
    #[derive(HowMuchWhere)]
    #[howmuchwhere(__hmw_internal_use)]
    #[repr(u8)]
    enum Test {
        A,
        _B,
        _C,
    }

    assert_eq!(
        Test::A.how_much_where(),
        CollectionResult {
            root: hash_map!{ path![:Test.data] => 1 },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_derive_enum_c() {
    #[derive(HowMuchWhere)]
    #[howmuchwhere(__hmw_internal_use)]
    #[repr(C)]
    enum Test {
        A,
        B(u8),
        _C,
    }

    assert_eq!(
        Test::A.how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:Test/A+overhead.internal_padding_and_unused] => mem::size_of::<Test>() - mem::size_of::<c_int>(),
                path![:Test/A+overhead.tag_size] => mem::size_of::<c_int>(),
            },
            shared: HashMap::new(),
        }
    );

    assert_eq!(
        Test::B(0).how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:Test/B+overhead.internal_padding_and_unused] => mem::size_of::<Test>() - mem::size_of::<c_int>() - 1,
                path![:Test/B+overhead.tag_size] => mem::size_of::<c_int>(),
                path![:Test/B.wrapped :u8.value] => 1,
            },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_derive_enum_u8() {
    #[derive(HowMuchWhere)]
    #[howmuchwhere(__hmw_internal_use)]
    #[repr(u8)]
    enum Test {
        A,
        B(u8),
        _C,
    }

    assert_eq!(
        Test::A.how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:Test/A+overhead.internal_padding_and_unused] => 1,
                path![:Test/A+overhead.tag_size] => 1,
            },
            shared: HashMap::new(),
        }
    );

    assert_eq!(
        Test::B(0).how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:Test/B+overhead.tag_size] => 1,
                path![:Test/B.wrapped :u8.value] => 1,
            },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_struct() {
    #[derive(HowMuchWhere)]
    #[howmuchwhere(__hmw_internal_use)]
    #[repr(C)]  // so we know the padding
    struct Test {
        x: u8,
        #[howmuchwhere(category="c")] y: u16,
    }

    let test = Test { x: 1, y: 2 };

    test.how_much_where();

    assert_eq!(
        test.how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:Test.x :u8.value] => 1,
                path![:Test+c.y :u16.value] => 2,
                path![:Test+overhead.internal_padding] => 1,
            },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_shared_reanchor_root() {
    use std::rc::Rc;

    assert_eq!(
        Rc::new(0usize).how_much_where(),
        CollectionResult {
            root: hash_map!{
                path![:(Rc<usize>)+overhead.inline_overhead] => PTR_SIZE,
                path![:(Rc<usize>).alloc :(RcBox<usize>)+overhead.alloc_overhead] => 2 * PTR_SIZE,
                path![:(Rc<usize>).alloc :(RcBox<usize>).referenced :usize.value] => PTR_SIZE,
            },
            shared: HashMap::new(),
        }
    );
}

#[test]
fn test_shared_cycle() {
    use std::cell::RefCell;
    use std::rc::Rc;

    type Main = Rc<RefCell<Option<Rc<UncycleTypes>>>>;
    struct UncycleTypes(Main);
    impl HowMuchWhere for UncycleTypes {
        fn how_much_where_impl(&self, collector: &mut Collector) {
            self.0.how_much_where_impl(collector);
        }
    }

    let main = Rc::new(RefCell::new(None));
    let other = Rc::new(UncycleTypes(main.clone()));
    *main.borrow_mut() = Some(other.clone());
    mem::drop(other);

    assert_eq!(
        main.how_much_where().root,
        hash_map!{ path![:Main+overhead.inline_overhead] => PTR_SIZE }
    );

    // The cycle gets inlined from `other` into `main`
    assert_eq!(main.how_much_where().shared.len(), 1);

    assert_eq!(
        main.how_much_where().total_size(),
        PTR_SIZE +  // main Rc inline overhead (alloc overhead is shared!)
            PTR_SIZE * 3 * 2 +  // allocated Rc overhead
            PTR_SIZE +  // refcell overhead
            0  // option doesn't take up extra space because of the non-null pointer inside of `Rc`
    );
}
