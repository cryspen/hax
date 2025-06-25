pub use super::root;
pub mod alloc {
    #![doc = r##"This is the module [`::alloc`]."##]
    pub use super::root;
    pub mod alloc {
        #![doc = r##"This is the module [`::alloc::alloc`]."##]
        pub use super::root;
        mk!(
            Global,
            r##"This is the struct [`::alloc::alloc::Global`]."##,
            r##"["alloc",[[{"TypeNs":"alloc"},0],[{"TypeNs":"Global"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::alloc::alloc())
        );
        mk!(
            Impl__1,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"alloc"},0],["Impl",1]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::alloc())
        );
        mk!(
            Impl__3,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"alloc"},0],["Impl",3]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::alloc())
        );
    }
    pub mod boxed {
        #![doc = r##"This is the module [`::alloc::boxed`]."##]
        pub use super::root;
        mk!(
            Box,
            r##"This is the struct [`::alloc::boxed::Box`]."##,
            r##"["alloc",[[{"TypeNs":"boxed"},0],[{"TypeNs":"Box"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::alloc::boxed())
        );
    }
    pub mod slice {
        #![doc = r##"This is the module [`::alloc::slice`]."##]
        pub use super::root;
        pub mod Concat {
            #![doc = r##"This is the trait [`::alloc::slice::Concat`]."##]
            pub use super::root;
            mk!(
                Output,
                r##"This is the associated type [`::alloc::slice::Concat::Output`]."##,
                r##"["alloc",[[{"TypeNs":"slice"},0],[{"TypeNs":"Concat"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                ::core::option::Option::Some(root::alloc::slice::Concat())
            );
        }
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                concat,
                r##"This is the associated function [`::alloc::slice::Impl::concat`]."##,
                r##"["alloc",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"concat"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::alloc::slice::Impl())
            );
            mk!(
                into_vec,
                r##"This is the associated function [`::alloc::slice::Impl::into_vec`]."##,
                r##"["alloc",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"into_vec"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::alloc::slice::Impl())
            );
            mk!(
                to_vec,
                r##"This is the associated function [`::alloc::slice::Impl::to_vec`]."##,
                r##"["alloc",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"to_vec"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::alloc::slice::Impl())
            );
        }
        mk!(
            Concat,
            r##"This is the trait [`::alloc::slice::Concat`]."##,
            r##"["alloc",[[{"TypeNs":"slice"},0],[{"TypeNs":"Concat"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::alloc::slice())
        );
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"slice"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::alloc::slice())
        );
        mk!(
            Impl__2,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"slice"},0],["Impl",2]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::slice())
        );
    }
    pub mod string {
        #![doc = r##"This is the module [`::alloc::string`]."##]
        pub use super::root;
        mk!(
            String,
            r##"This is the struct [`::alloc::string::String`]."##,
            r##"["alloc",[[{"TypeNs":"string"},0],[{"TypeNs":"String"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::alloc::string())
        );
    }
    pub mod vec {
        #![doc = r##"This is the module [`::alloc::vec`]."##]
        pub use super::root;
        pub mod Impl__1 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                truncate,
                r##"This is the associated function [`::alloc::vec::Impl__1::truncate`]."##,
                r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",1],[{"ValueNs":"truncate"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::alloc::vec::Impl__1())
            );
        }
        pub mod Impl__2 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                extend_from_slice,
                r##"This is the associated function [`::alloc::vec::Impl__2::extend_from_slice`]."##,
                r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",2],[{"ValueNs":"extend_from_slice"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::alloc::vec::Impl__2())
            );
        }
        mk!(
            Impl__1,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",1]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            Impl__11,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",11]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            Impl__13,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",13]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            Impl__2,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",2]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            Impl__8,
            r##"This is a impl block."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],["Impl",8]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            Vec,
            r##"This is the struct [`::alloc::vec::Vec`]."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],[{"TypeNs":"Vec"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
        mk!(
            from_elem,
            r##"This is the function [`::alloc::vec::from_elem`]."##,
            r##"["alloc",[[{"TypeNs":"vec"},0],[{"ValueNs":"from_elem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::alloc::vec())
        );
    }
    mk!(
        alloc,
        r##"This is the module [`::alloc::alloc`]."##,
        r##"["alloc",[[{"TypeNs":"alloc"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::alloc())
    );
    mk!(
        boxed,
        r##"This is the module [`::alloc::boxed`]."##,
        r##"["alloc",[[{"TypeNs":"boxed"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::alloc())
    );
    mk!(
        slice,
        r##"This is the module [`::alloc::slice`]."##,
        r##"["alloc",[[{"TypeNs":"slice"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::alloc())
    );
    mk!(
        string,
        r##"This is the module [`::alloc::string`]."##,
        r##"["alloc",[[{"TypeNs":"string"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::alloc())
    );
    mk!(
        vec,
        r##"This is the module [`::alloc::vec`]."##,
        r##"["alloc",[[{"TypeNs":"vec"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::alloc())
    );
}
pub mod core {
    #![doc = r##"This is the module [`::core`]."##]
    pub use super::root;
    pub mod alloc {
        #![doc = r##"This is the module [`::core::alloc`]."##]
        pub use super::root;
        mk!(
            Allocator,
            r##"This is the trait [`::core::alloc::Allocator`]."##,
            r##"["core",[[{"TypeNs":"alloc"},0],[{"TypeNs":"Allocator"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::alloc())
        );
    }
    pub mod array {
        #![doc = r##"This is the module [`::core::array`]."##]
        pub use super::root;
        pub mod iter {
            #![doc = r##"This is the module [`::core::array::iter`]."##]
            pub use super::root;
            mk!(
                Impl__1,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"array"},0],[{"TypeNs":"iter"},0],["Impl",1]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::array::iter())
            );
            mk!(
                IntoIter,
                r##"This is the struct [`::core::array::iter::IntoIter`]."##,
                r##"["core",[[{"TypeNs":"array"},0],[{"TypeNs":"iter"},0],[{"TypeNs":"IntoIter"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::array::iter())
            );
        }
        mk!(
            iter,
            r##"This is the module [`::core::array::iter`]."##,
            r##"["core",[[{"TypeNs":"array"},0],[{"TypeNs":"iter"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::array())
        );
    }
    pub mod borrow {
        #![doc = r##"This is the module [`::core::borrow`]."##]
        pub use super::root;
        mk!(
            Borrow,
            r##"This is the trait [`::core::borrow::Borrow`]."##,
            r##"["core",[[{"TypeNs":"borrow"},0],[{"TypeNs":"Borrow"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::borrow())
        );
        mk!(
            Impl__2,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"borrow"},0],["Impl",2]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::core::borrow())
        );
    }
    pub mod clone {
        #![doc = r##"This is the module [`::core::clone`]."##]
        pub use super::root;
        pub mod Clone {
            #![doc = r##"This is the trait [`::core::clone::Clone`]."##]
            pub use super::root;
            mk!(
                clone,
                r##"This is the associated function [`::core::clone::Clone::clone`]."##,
                r##"["core",[[{"TypeNs":"clone"},0],[{"TypeNs":"Clone"},0],[{"ValueNs":"clone"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::clone::Clone())
            );
        }
        pub mod impls {
            #![doc = r##"This is the module [`::core::clone::impls`]."##]
            pub use super::root;
            mk!(
                Impl__6,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"clone"},0],[{"TypeNs":"impls"},0],["Impl",6]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::clone::impls())
            );
        }
        mk!(
            Clone,
            r##"This is the trait [`::core::clone::Clone`]."##,
            r##"["core",[[{"TypeNs":"clone"},0],[{"TypeNs":"Clone"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::clone())
        );
        mk!(
            impls,
            r##"This is the module [`::core::clone::impls`]."##,
            r##"["core",[[{"TypeNs":"clone"},0],[{"TypeNs":"impls"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::clone())
        );
    }
    pub mod cmp {
        #![doc = r##"This is the module [`::core::cmp`]."##]
        pub use super::root;
        pub mod PartialEq {
            #![doc = r##"This is the trait [`::core::cmp::PartialEq`]."##]
            pub use super::root;
            mk!(
                eq,
                r##"This is the associated function [`::core::cmp::PartialEq::eq`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialEq"},0],[{"ValueNs":"eq"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialEq())
            );
            mk!(
                ne,
                r##"This is the associated function [`::core::cmp::PartialEq::ne`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialEq"},0],[{"ValueNs":"ne"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialEq())
            );
        }
        pub mod PartialOrd {
            #![doc = r##"This is the trait [`::core::cmp::PartialOrd`]."##]
            pub use super::root;
            mk!(
                ge,
                r##"This is the associated function [`::core::cmp::PartialOrd::ge`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialOrd"},0],[{"ValueNs":"ge"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialOrd())
            );
            mk!(
                gt,
                r##"This is the associated function [`::core::cmp::PartialOrd::gt`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialOrd"},0],[{"ValueNs":"gt"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialOrd())
            );
            mk!(
                le,
                r##"This is the associated function [`::core::cmp::PartialOrd::le`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialOrd"},0],[{"ValueNs":"le"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialOrd())
            );
            mk!(
                lt,
                r##"This is the associated function [`::core::cmp::PartialOrd::lt`]."##,
                r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialOrd"},0],[{"ValueNs":"lt"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::cmp::PartialOrd())
            );
        }
        mk!(
            PartialEq,
            r##"This is the trait [`::core::cmp::PartialEq`]."##,
            r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialEq"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::cmp())
        );
        mk!(
            PartialOrd,
            r##"This is the trait [`::core::cmp::PartialOrd`]."##,
            r##"["core",[[{"TypeNs":"cmp"},0],[{"TypeNs":"PartialOrd"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::cmp())
        );
    }
    pub mod convert {
        #![doc = r##"This is the module [`::core::convert`]."##]
        pub use super::root;
        pub mod From {
            #![doc = r##"This is the trait [`::core::convert::From`]."##]
            pub use super::root;
            mk!(
                from,
                r##"This is the associated function [`::core::convert::From::from`]."##,
                r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"From"},0],[{"ValueNs":"from"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::convert::From())
            );
        }
        pub mod Into {
            #![doc = r##"This is the trait [`::core::convert::Into`]."##]
            pub use super::root;
            mk!(
                into,
                r##"This is the associated function [`::core::convert::Into::into`]."##,
                r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"Into"},0],[{"ValueNs":"into"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::convert::Into())
            );
        }
        pub mod num {
            #![doc = r##"This is the module [`::core::convert::num`]."##]
            pub use super::root;
            mk!(
                Impl__64,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"num"},0],["Impl",64]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::convert::num())
            );
            mk!(
                Impl__88,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"num"},0],["Impl",88]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::convert::num())
            );
        }
        mk!(
            From,
            r##"This is the trait [`::core::convert::From`]."##,
            r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"From"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::convert())
        );
        mk!(
            Impl__3,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"convert"},0],["Impl",3]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::core::convert())
        );
        mk!(
            Infallible,
            r##"This is the enum [`::core::convert::Infallible`]."##,
            r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"Infallible"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::core::convert())
        );
        mk!(
            Into,
            r##"This is the trait [`::core::convert::Into`]."##,
            r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"Into"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::convert())
        );
        mk!(
            num,
            r##"This is the module [`::core::convert::num`]."##,
            r##"["core",[[{"TypeNs":"convert"},0],[{"TypeNs":"num"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::convert())
        );
    }
    pub mod iter {
        #![doc = r##"This is the module [`::core::iter`]."##]
        pub use super::root;
        pub mod adapters {
            #![doc = r##"This is the module [`::core::iter::adapters`]."##]
            pub use super::root;
            pub mod enumerate {
                #![doc = r##"This is the module [`::core::iter::adapters::enumerate`]."##]
                pub use super::root;
                mk!(
                    Enumerate,
                    r##"This is the struct [`::core::iter::adapters::enumerate::Enumerate`]."##,
                    r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"adapters"},0],[{"TypeNs":"enumerate"},0],[{"TypeNs":"Enumerate"},0]],"Struct"]"##,
                    ::core::option::Option::Some(root::core::iter::adapters::enumerate())
                );
            }
            pub mod step_by {
                #![doc = r##"This is the module [`::core::iter::adapters::step_by`]."##]
                pub use super::root;
                mk!(
                    StepBy,
                    r##"This is the struct [`::core::iter::adapters::step_by::StepBy`]."##,
                    r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"adapters"},0],[{"TypeNs":"step_by"},0],[{"TypeNs":"StepBy"},0]],"Struct"]"##,
                    ::core::option::Option::Some(root::core::iter::adapters::step_by())
                );
            }
            mk!(
                enumerate,
                r##"This is the module [`::core::iter::adapters::enumerate`]."##,
                r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"adapters"},0],[{"TypeNs":"enumerate"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::core::iter::adapters())
            );
            mk!(
                step_by,
                r##"This is the module [`::core::iter::adapters::step_by`]."##,
                r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"adapters"},0],[{"TypeNs":"step_by"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::core::iter::adapters())
            );
        }
        pub mod traits {
            #![doc = r##"This is the module [`::core::iter::traits`]."##]
            pub use super::root;
            pub mod collect {
                #![doc = r##"This is the module [`::core::iter::traits::collect`]."##]
                pub use super::root;
                pub mod IntoIterator {
                    #![doc = r##"This is the trait [`::core::iter::traits::collect::IntoIterator`]."##]
                    pub use super::root;
                    mk!(
                        IntoIter,
                        r##"This is the associated type [`::core::iter::traits::collect::IntoIterator::IntoIter`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"collect"},0],[{"TypeNs":"IntoIterator"},0],[{"TypeNs":"IntoIter"},0]],"AssocTy"]"##,
                        ::core::option::Option::Some(
                            root::core::iter::traits::collect::IntoIterator()
                        )
                    );
                    mk!(
                        into_iter,
                        r##"This is the associated function [`::core::iter::traits::collect::IntoIterator::into_iter`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"collect"},0],[{"TypeNs":"IntoIterator"},0],[{"ValueNs":"into_iter"},0]],"AssocFn"]"##,
                        ::core::option::Option::Some(
                            root::core::iter::traits::collect::IntoIterator()
                        )
                    );
                }
                mk!(
                    IntoIterator,
                    r##"This is the trait [`::core::iter::traits::collect::IntoIterator`]."##,
                    r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"collect"},0],[{"TypeNs":"IntoIterator"},0]],"Trait"]"##,
                    ::core::option::Option::Some(root::core::iter::traits::collect())
                );
            }
            pub mod iterator {
                #![doc = r##"This is the module [`::core::iter::traits::iterator`]."##]
                pub use super::root;
                pub mod Iterator {
                    #![doc = r##"This is the trait [`::core::iter::traits::iterator::Iterator`]."##]
                    pub use super::root;
                    mk!(
                        Item,
                        r##"This is the associated type [`::core::iter::traits::iterator::Iterator::Item`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0],[{"TypeNs":"Item"},0]],"AssocTy"]"##,
                        ::core::option::Option::Some(root::core::iter::traits::iterator::Iterator())
                    );
                    mk!(
                        enumerate,
                        r##"This is the associated function [`::core::iter::traits::iterator::Iterator::enumerate`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0],[{"ValueNs":"enumerate"},0]],"AssocFn"]"##,
                        ::core::option::Option::Some(root::core::iter::traits::iterator::Iterator())
                    );
                    mk!(
                        fold,
                        r##"This is the associated function [`::core::iter::traits::iterator::Iterator::fold`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0],[{"ValueNs":"fold"},0]],"AssocFn"]"##,
                        ::core::option::Option::Some(root::core::iter::traits::iterator::Iterator())
                    );
                    mk!(
                        next,
                        r##"This is the associated function [`::core::iter::traits::iterator::Iterator::next`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0],[{"ValueNs":"next"},0]],"AssocFn"]"##,
                        ::core::option::Option::Some(root::core::iter::traits::iterator::Iterator())
                    );
                    mk!(
                        step_by,
                        r##"This is the associated function [`::core::iter::traits::iterator::Iterator::step_by`]."##,
                        r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0],[{"ValueNs":"step_by"},0]],"AssocFn"]"##,
                        ::core::option::Option::Some(root::core::iter::traits::iterator::Iterator())
                    );
                }
                mk!(
                    Iterator,
                    r##"This is the trait [`::core::iter::traits::iterator::Iterator`]."##,
                    r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0],[{"TypeNs":"Iterator"},0]],"Trait"]"##,
                    ::core::option::Option::Some(root::core::iter::traits::iterator())
                );
            }
            mk!(
                collect,
                r##"This is the module [`::core::iter::traits::collect`]."##,
                r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"collect"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::core::iter::traits())
            );
            mk!(
                iterator,
                r##"This is the module [`::core::iter::traits::iterator`]."##,
                r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0],[{"TypeNs":"iterator"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::core::iter::traits())
            );
        }
        mk!(
            adapters,
            r##"This is the module [`::core::iter::adapters`]."##,
            r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"adapters"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::iter())
        );
        mk!(
            traits,
            r##"This is the module [`::core::iter::traits`]."##,
            r##"["core",[[{"TypeNs":"iter"},0],[{"TypeNs":"traits"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::iter())
        );
    }
    pub mod marker {
        #![doc = r##"This is the module [`::core::marker`]."##]
        pub use super::root;
        mk!(
            Copy,
            r##"This is the trait [`::core::marker::Copy`]."##,
            r##"["core",[[{"TypeNs":"marker"},0],[{"TypeNs":"Copy"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::marker())
        );
        mk!(
            Sized,
            r##"This is the trait [`::core::marker::Sized`]."##,
            r##"["core",[[{"TypeNs":"marker"},0],[{"TypeNs":"Sized"},0]],"Trait"]"##,
            ::core::option::Option::Some(root::core::marker())
        );
    }
    pub mod num {
        #![doc = r##"This is the module [`::core::num`]."##]
        pub use super::root;
        pub mod Impl__9 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                to_le_bytes,
                r##"This is the associated function [`::core::num::Impl__9::to_le_bytes`]."##,
                r##"["core",[[{"TypeNs":"num"},0],["Impl",9],[{"ValueNs":"to_le_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::num::Impl__9())
            );
        }
        mk!(
            Impl__9,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"num"},0],["Impl",9]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::core::num())
        );
    }
    pub mod ops {
        #![doc = r##"This is the module [`::core::ops`]."##]
        pub use super::root;
        pub mod arith {
            #![doc = r##"This is the module [`::core::ops::arith`]."##]
            pub use super::root;
            pub mod Add {
                #![doc = r##"This is the trait [`::core::ops::arith::Add`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Add::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Add"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Add())
                );
                mk!(
                    add,
                    r##"This is the associated function [`::core::ops::arith::Add::add`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Add"},0],[{"ValueNs":"add"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Add())
                );
            }
            pub mod Div {
                #![doc = r##"This is the trait [`::core::ops::arith::Div`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Div::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Div"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Div())
                );
                mk!(
                    div,
                    r##"This is the associated function [`::core::ops::arith::Div::div`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Div"},0],[{"ValueNs":"div"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Div())
                );
            }
            pub mod Mul {
                #![doc = r##"This is the trait [`::core::ops::arith::Mul`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Mul::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Mul"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Mul())
                );
                mk!(
                    mul,
                    r##"This is the associated function [`::core::ops::arith::Mul::mul`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Mul"},0],[{"ValueNs":"mul"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Mul())
                );
            }
            pub mod Neg {
                #![doc = r##"This is the trait [`::core::ops::arith::Neg`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Neg::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Neg"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Neg())
                );
                mk!(
                    neg,
                    r##"This is the associated function [`::core::ops::arith::Neg::neg`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Neg"},0],[{"ValueNs":"neg"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Neg())
                );
            }
            pub mod Rem {
                #![doc = r##"This is the trait [`::core::ops::arith::Rem`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Rem::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Rem"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Rem())
                );
                mk!(
                    rem,
                    r##"This is the associated function [`::core::ops::arith::Rem::rem`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Rem"},0],[{"ValueNs":"rem"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Rem())
                );
            }
            pub mod Sub {
                #![doc = r##"This is the trait [`::core::ops::arith::Sub`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::arith::Sub::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Sub"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Sub())
                );
                mk!(
                    sub,
                    r##"This is the associated function [`::core::ops::arith::Sub::sub`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Sub"},0],[{"ValueNs":"sub"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::arith::Sub())
                );
            }
            mk!(
                Add,
                r##"This is the trait [`::core::ops::arith::Add`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Add"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
            mk!(
                Div,
                r##"This is the trait [`::core::ops::arith::Div`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Div"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
            mk!(
                Mul,
                r##"This is the trait [`::core::ops::arith::Mul`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Mul"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
            mk!(
                Neg,
                r##"This is the trait [`::core::ops::arith::Neg`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Neg"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
            mk!(
                Rem,
                r##"This is the trait [`::core::ops::arith::Rem`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Rem"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
            mk!(
                Sub,
                r##"This is the trait [`::core::ops::arith::Sub`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0],[{"TypeNs":"Sub"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::arith())
            );
        }
        pub mod bit {
            #![doc = r##"This is the module [`::core::ops::bit`]."##]
            pub use super::root;
            pub mod BitAnd {
                #![doc = r##"This is the trait [`::core::ops::bit::BitAnd`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::BitAnd::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitAnd"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitAnd())
                );
                mk!(
                    bitand,
                    r##"This is the associated function [`::core::ops::bit::BitAnd::bitand`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitAnd"},0],[{"ValueNs":"bitand"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitAnd())
                );
            }
            pub mod BitOr {
                #![doc = r##"This is the trait [`::core::ops::bit::BitOr`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::BitOr::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitOr"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitOr())
                );
                mk!(
                    bitor,
                    r##"This is the associated function [`::core::ops::bit::BitOr::bitor`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitOr"},0],[{"ValueNs":"bitor"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitOr())
                );
            }
            pub mod BitXor {
                #![doc = r##"This is the trait [`::core::ops::bit::BitXor`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::BitXor::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitXor"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitXor())
                );
                mk!(
                    bitxor,
                    r##"This is the associated function [`::core::ops::bit::BitXor::bitxor`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitXor"},0],[{"ValueNs":"bitxor"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::BitXor())
                );
            }
            pub mod Not {
                #![doc = r##"This is the trait [`::core::ops::bit::Not`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::Not::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Not"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Not())
                );
                mk!(
                    not,
                    r##"This is the associated function [`::core::ops::bit::Not::not`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Not"},0],[{"ValueNs":"not"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Not())
                );
            }
            pub mod Shl {
                #![doc = r##"This is the trait [`::core::ops::bit::Shl`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::Shl::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shl"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Shl())
                );
                mk!(
                    shl,
                    r##"This is the associated function [`::core::ops::bit::Shl::shl`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shl"},0],[{"ValueNs":"shl"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Shl())
                );
            }
            pub mod Shr {
                #![doc = r##"This is the trait [`::core::ops::bit::Shr`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::bit::Shr::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shr"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Shr())
                );
                mk!(
                    shr,
                    r##"This is the associated function [`::core::ops::bit::Shr::shr`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shr"},0],[{"ValueNs":"shr"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::bit::Shr())
                );
            }
            mk!(
                BitAnd,
                r##"This is the trait [`::core::ops::bit::BitAnd`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitAnd"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
            mk!(
                BitOr,
                r##"This is the trait [`::core::ops::bit::BitOr`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitOr"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
            mk!(
                BitXor,
                r##"This is the trait [`::core::ops::bit::BitXor`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"BitXor"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
            mk!(
                Not,
                r##"This is the trait [`::core::ops::bit::Not`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Not"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
            mk!(
                Shl,
                r##"This is the trait [`::core::ops::bit::Shl`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shl"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
            mk!(
                Shr,
                r##"This is the trait [`::core::ops::bit::Shr`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0],[{"TypeNs":"Shr"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::bit())
            );
        }
        pub mod control_flow {
            #![doc = r##"This is the module [`::core::ops::control_flow`]."##]
            pub use super::root;
            pub mod ControlFlow {
                #![doc = r##"This is the enum [`::core::ops::control_flow::ControlFlow`]."##]
                pub use super::root;
                pub mod Break {
                    #![doc = r##"This is the variant [`::core::ops::control_flow::ControlFlow::Break`]."##]
                    pub use super::root;
                    mk!(
                        _0,
                        r##"This is the field [`_0`] from ::core::ops::control_flow::ControlFlow::Break."##,
                        r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0],[{"TypeNs":"ControlFlow"},0],[{"TypeNs":"Break"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                        ::core::option::Option::Some(
                            root::core::ops::control_flow::ControlFlow::Break()
                        )
                    );
                }
                pub mod Continue {
                    #![doc = r##"This is the variant [`::core::ops::control_flow::ControlFlow::Continue`]."##]
                    pub use super::root;
                    mk!(
                        _0,
                        r##"This is the field [`_0`] from ::core::ops::control_flow::ControlFlow::Continue."##,
                        r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0],[{"TypeNs":"ControlFlow"},0],[{"TypeNs":"Continue"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                        ::core::option::Option::Some(
                            root::core::ops::control_flow::ControlFlow::Continue()
                        )
                    );
                }
                mk!(
                    Break,
                    r##"This is the variant [`::core::ops::control_flow::ControlFlow::Break`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0],[{"TypeNs":"ControlFlow"},0],[{"TypeNs":"Break"},0]],"Variant"]"##,
                    ::core::option::Option::Some(root::core::ops::control_flow::ControlFlow())
                );
                mk!(
                    Continue,
                    r##"This is the variant [`::core::ops::control_flow::ControlFlow::Continue`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0],[{"TypeNs":"ControlFlow"},0],[{"TypeNs":"Continue"},0]],"Variant"]"##,
                    ::core::option::Option::Some(root::core::ops::control_flow::ControlFlow())
                );
            }
            mk!(
                ControlFlow,
                r##"This is the enum [`::core::ops::control_flow::ControlFlow`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0],[{"TypeNs":"ControlFlow"},0]],"Enum"]"##,
                ::core::option::Option::Some(root::core::ops::control_flow())
            );
        }
        pub mod deref {
            #![doc = r##"This is the module [`::core::ops::deref`]."##]
            pub use super::root;
            pub mod Deref {
                #![doc = r##"This is the trait [`::core::ops::deref::Deref`]."##]
                pub use super::root;
                mk!(
                    Target,
                    r##"This is the associated type [`::core::ops::deref::Deref::Target`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"deref"},0],[{"TypeNs":"Deref"},0],[{"TypeNs":"Target"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::deref::Deref())
                );
                mk!(
                    deref,
                    r##"This is the associated function [`::core::ops::deref::Deref::deref`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"deref"},0],[{"TypeNs":"Deref"},0],[{"ValueNs":"deref"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::deref::Deref())
                );
            }
            mk!(
                Deref,
                r##"This is the trait [`::core::ops::deref::Deref`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"deref"},0],[{"TypeNs":"Deref"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::deref())
            );
            mk!(
                DerefMut,
                r##"This is the trait [`::core::ops::deref::DerefMut`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"deref"},0],[{"TypeNs":"DerefMut"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::deref())
            );
        }
        pub mod function {
            #![doc = r##"This is the module [`::core::ops::function`]."##]
            pub use super::root;
            mk!(
                Fn,
                r##"This is the trait [`::core::ops::function::Fn`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"function"},0],[{"TypeNs":"Fn"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::function())
            );
            mk!(
                FnMut,
                r##"This is the trait [`::core::ops::function::FnMut`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"function"},0],[{"TypeNs":"FnMut"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::function())
            );
            mk!(
                FnOnce,
                r##"This is the trait [`::core::ops::function::FnOnce`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"function"},0],[{"TypeNs":"FnOnce"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::function())
            );
        }
        pub mod index {
            #![doc = r##"This is the module [`::core::ops::index`]."##]
            pub use super::root;
            pub mod Index {
                #![doc = r##"This is the trait [`::core::ops::index::Index`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::index::Index::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"index"},0],[{"TypeNs":"Index"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::index::Index())
                );
                mk!(
                    index,
                    r##"This is the associated function [`::core::ops::index::Index::index`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"index"},0],[{"TypeNs":"Index"},0],[{"ValueNs":"index"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::index::Index())
                );
            }
            mk!(
                Index,
                r##"This is the trait [`::core::ops::index::Index`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"index"},0],[{"TypeNs":"Index"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::index())
            );
        }
        pub mod range {
            #![doc = r##"This is the module [`::core::ops::range`]."##]
            pub use super::root;
            pub mod Range {
                #![doc = r##"This is the struct [`::core::ops::range::Range`]."##]
                pub use super::root;
                mk!(
                    end,
                    r##"This is the field [`end`] from ::core::ops::range::Range."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"Range"},0],[{"ValueNs":"end"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::ops::range::Range())
                );
                mk!(
                    start,
                    r##"This is the field [`start`] from ::core::ops::range::Range."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"Range"},0],[{"ValueNs":"start"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::ops::range::Range())
                );
            }
            pub mod RangeFrom {
                #![doc = r##"This is the struct [`::core::ops::range::RangeFrom`]."##]
                pub use super::root;
                mk!(
                    start,
                    r##"This is the field [`start`] from ::core::ops::range::RangeFrom."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"RangeFrom"},0],[{"ValueNs":"start"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::ops::range::RangeFrom())
                );
            }
            pub mod RangeTo {
                #![doc = r##"This is the struct [`::core::ops::range::RangeTo`]."##]
                pub use super::root;
                mk!(
                    end,
                    r##"This is the field [`end`] from ::core::ops::range::RangeTo."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"RangeTo"},0],[{"ValueNs":"end"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::ops::range::RangeTo())
                );
            }
            mk!(
                Range,
                r##"This is the struct [`::core::ops::range::Range`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"Range"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::ops::range())
            );
            mk!(
                RangeFrom,
                r##"This is the struct [`::core::ops::range::RangeFrom`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"RangeFrom"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::ops::range())
            );
            mk!(
                RangeFull,
                r##"This is the struct [`::core::ops::range::RangeFull`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"RangeFull"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::ops::range())
            );
            mk!(
                RangeTo,
                r##"This is the struct [`::core::ops::range::RangeTo`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0],[{"TypeNs":"RangeTo"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::ops::range())
            );
        }
        pub mod try_trait {
            #![doc = r##"This is the module [`::core::ops::try_trait`]."##]
            pub use super::root;
            pub mod FromResidual {
                #![doc = r##"This is the trait [`::core::ops::try_trait::FromResidual`]."##]
                pub use super::root;
                mk!(
                    from_residual,
                    r##"This is the associated function [`::core::ops::try_trait::FromResidual::from_residual`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"FromResidual"},0],[{"ValueNs":"from_residual"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::try_trait::FromResidual())
                );
            }
            pub mod Try {
                #![doc = r##"This is the trait [`::core::ops::try_trait::Try`]."##]
                pub use super::root;
                mk!(
                    Output,
                    r##"This is the associated type [`::core::ops::try_trait::Try::Output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"Try"},0],[{"TypeNs":"Output"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::try_trait::Try())
                );
                mk!(
                    Residual,
                    r##"This is the associated type [`::core::ops::try_trait::Try::Residual`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"Try"},0],[{"TypeNs":"Residual"},0]],"AssocTy"]"##,
                    ::core::option::Option::Some(root::core::ops::try_trait::Try())
                );
                mk!(
                    branch,
                    r##"This is the associated function [`::core::ops::try_trait::Try::branch`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"Try"},0],[{"ValueNs":"branch"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::try_trait::Try())
                );
                mk!(
                    from_output,
                    r##"This is the associated function [`::core::ops::try_trait::Try::from_output`]."##,
                    r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"Try"},0],[{"ValueNs":"from_output"},0]],"AssocFn"]"##,
                    ::core::option::Option::Some(root::core::ops::try_trait::Try())
                );
            }
            mk!(
                FromResidual,
                r##"This is the trait [`::core::ops::try_trait::FromResidual`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"FromResidual"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::try_trait())
            );
            mk!(
                Try,
                r##"This is the trait [`::core::ops::try_trait::Try`]."##,
                r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0],[{"TypeNs":"Try"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::ops::try_trait())
            );
        }
        mk!(
            arith,
            r##"This is the module [`::core::ops::arith`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"arith"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            bit,
            r##"This is the module [`::core::ops::bit`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"bit"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            control_flow,
            r##"This is the module [`::core::ops::control_flow`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"control_flow"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            deref,
            r##"This is the module [`::core::ops::deref`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"deref"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            function,
            r##"This is the module [`::core::ops::function`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"function"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            index,
            r##"This is the module [`::core::ops::index`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"index"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            range,
            r##"This is the module [`::core::ops::range`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"range"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
        mk!(
            try_trait,
            r##"This is the module [`::core::ops::try_trait`]."##,
            r##"["core",[[{"TypeNs":"ops"},0],[{"TypeNs":"try_trait"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::ops())
        );
    }
    pub mod option {
        #![doc = r##"This is the module [`::core::option`]."##]
        pub use super::root;
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                is_some,
                r##"This is the associated function [`::core::option::Impl::is_some`]."##,
                r##"["core",[[{"TypeNs":"option"},0],["Impl",0],[{"ValueNs":"is_some"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::option::Impl())
            );
        }
        pub mod Option {
            #![doc = r##"This is the enum [`::core::option::Option`]."##]
            pub use super::root;
            pub mod Some {
                #![doc = r##"This is the variant [`::core::option::Option::Some`]."##]
                pub use super::root;
                mk!(
                    _0,
                    r##"This is the field [`_0`] from ::core::option::Option::Some."##,
                    r##"["core",[[{"TypeNs":"option"},0],[{"TypeNs":"Option"},0],[{"TypeNs":"Some"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::option::Option::Some())
                );
            }
            mk!(
                None,
                r##"This is the variant [`::core::option::Option::None`]."##,
                r##"["core",[[{"TypeNs":"option"},0],[{"TypeNs":"Option"},0],[{"TypeNs":"None"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::core::option::Option())
            );
            mk!(
                Some,
                r##"This is the variant [`::core::option::Option::Some`]."##,
                r##"["core",[[{"TypeNs":"option"},0],[{"TypeNs":"Option"},0],[{"TypeNs":"Some"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::core::option::Option())
            );
        }
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"option"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::core::option())
        );
        mk!(
            Option,
            r##"This is the enum [`::core::option::Option`]."##,
            r##"["core",[[{"TypeNs":"option"},0],[{"TypeNs":"Option"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::core::option())
        );
    }
    pub mod result {
        #![doc = r##"This is the module [`::core::result`]."##]
        pub use super::root;
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                map_err,
                r##"This is the associated function [`::core::result::Impl::map_err`]."##,
                r##"["core",[[{"TypeNs":"result"},0],["Impl",0],[{"ValueNs":"map_err"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::result::Impl())
            );
        }
        pub mod Result {
            #![doc = r##"This is the enum [`::core::result::Result`]."##]
            pub use super::root;
            pub mod Err {
                #![doc = r##"This is the variant [`::core::result::Result::Err`]."##]
                pub use super::root;
                mk!(
                    _0,
                    r##"This is the field [`_0`] from ::core::result::Result::Err."##,
                    r##"["core",[[{"TypeNs":"result"},0],[{"TypeNs":"Result"},0],[{"TypeNs":"Err"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::result::Result::Err())
                );
            }
            pub mod Ok {
                #![doc = r##"This is the variant [`::core::result::Result::Ok`]."##]
                pub use super::root;
                mk!(
                    _0,
                    r##"This is the field [`_0`] from ::core::result::Result::Ok."##,
                    r##"["core",[[{"TypeNs":"result"},0],[{"TypeNs":"Result"},0],[{"TypeNs":"Ok"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                    ::core::option::Option::Some(root::core::result::Result::Ok())
                );
            }
            mk!(
                Err,
                r##"This is the variant [`::core::result::Result::Err`]."##,
                r##"["core",[[{"TypeNs":"result"},0],[{"TypeNs":"Result"},0],[{"TypeNs":"Err"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::core::result::Result())
            );
            mk!(
                Ok,
                r##"This is the variant [`::core::result::Result::Ok`]."##,
                r##"["core",[[{"TypeNs":"result"},0],[{"TypeNs":"Result"},0],[{"TypeNs":"Ok"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::core::result::Result())
            );
        }
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"result"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::core::result())
        );
        mk!(
            Impl__28,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"result"},0],["Impl",28]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::core::result())
        );
        mk!(
            Result,
            r##"This is the enum [`::core::result::Result`]."##,
            r##"["core",[[{"TypeNs":"result"},0],[{"TypeNs":"Result"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::core::result())
        );
    }
    pub mod slice {
        #![doc = r##"This is the module [`::core::slice`]."##]
        pub use super::root;
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                chunks_exact,
                r##"This is the associated function [`::core::slice::Impl::chunks_exact`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"chunks_exact"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::slice::Impl())
            );
            mk!(
                iter,
                r##"This is the associated function [`::core::slice::Impl::iter`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"iter"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::slice::Impl())
            );
            mk!(
                len,
                r##"This is the associated function [`::core::slice::Impl::len`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],["Impl",0],[{"ValueNs":"len"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::core::slice::Impl())
            );
        }
        pub mod index {
            #![doc = r##"This is the module [`::core::slice::index`]."##]
            pub use super::root;
            mk!(
                Impl__2,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"index"},0],["Impl",2]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::slice::index())
            );
            mk!(
                Impl__4,
                r##"This is a impl block."##,
                r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"index"},0],["Impl",4]],{"Impl":{"of_trait":true}}]"##,
                ::core::option::Option::Some(root::core::slice::index())
            );
            mk!(
                SliceIndex,
                r##"This is the trait [`::core::slice::index::SliceIndex`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"index"},0],[{"TypeNs":"SliceIndex"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::core::slice::index())
            );
        }
        pub mod iter {
            #![doc = r##"This is the module [`::core::slice::iter`]."##]
            pub use super::root;
            mk!(
                ChunksExact,
                r##"This is the struct [`::core::slice::iter::ChunksExact`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"iter"},0],[{"TypeNs":"ChunksExact"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::slice::iter())
            );
            mk!(
                Iter,
                r##"This is the struct [`::core::slice::iter::Iter`]."##,
                r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"iter"},0],[{"TypeNs":"Iter"},0]],"Struct"]"##,
                ::core::option::Option::Some(root::core::slice::iter())
            );
        }
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["core",[[{"TypeNs":"slice"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::core::slice())
        );
        mk!(
            index,
            r##"This is the module [`::core::slice::index`]."##,
            r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"index"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::slice())
        );
        mk!(
            iter,
            r##"This is the module [`::core::slice::iter`]."##,
            r##"["core",[[{"TypeNs":"slice"},0],[{"TypeNs":"iter"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::core::slice())
        );
    }
    mk!(
        alloc,
        r##"This is the module [`::core::alloc`]."##,
        r##"["core",[[{"TypeNs":"alloc"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        array,
        r##"This is the module [`::core::array`]."##,
        r##"["core",[[{"TypeNs":"array"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        borrow,
        r##"This is the module [`::core::borrow`]."##,
        r##"["core",[[{"TypeNs":"borrow"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        clone,
        r##"This is the module [`::core::clone`]."##,
        r##"["core",[[{"TypeNs":"clone"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        cmp,
        r##"This is the module [`::core::cmp`]."##,
        r##"["core",[[{"TypeNs":"cmp"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        convert,
        r##"This is the module [`::core::convert`]."##,
        r##"["core",[[{"TypeNs":"convert"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        iter,
        r##"This is the module [`::core::iter`]."##,
        r##"["core",[[{"TypeNs":"iter"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        marker,
        r##"This is the module [`::core::marker`]."##,
        r##"["core",[[{"TypeNs":"marker"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        num,
        r##"This is the module [`::core::num`]."##,
        r##"["core",[[{"TypeNs":"num"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        ops,
        r##"This is the module [`::core::ops`]."##,
        r##"["core",[[{"TypeNs":"ops"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        option,
        r##"This is the module [`::core::option`]."##,
        r##"["core",[[{"TypeNs":"option"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        result,
        r##"This is the module [`::core::result`]."##,
        r##"["core",[[{"TypeNs":"result"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
    mk!(
        slice,
        r##"This is the module [`::core::slice`]."##,
        r##"["core",[[{"TypeNs":"slice"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::core())
    );
}
pub mod hax_engine_names {
    #![doc = r##"This is the module [`::hax_engine_names`]."##]
    pub use super::root;
    pub mod crypto_abstractions {
        #![doc = r##"This is the module [`::hax_engine_names::crypto_abstractions`]."##]
        pub use super::root;
        mk!(
            Use,
            r##"This is the use item [`::hax_engine_names::crypto_abstractions::Use`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"crypto_abstractions"},0],["Use",0]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::crypto_abstractions())
        );
        mk!(
            crypto_abstractions,
            r##"This is the function [`::hax_engine_names::crypto_abstractions::crypto_abstractions`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"crypto_abstractions"},0],[{"ValueNs":"crypto_abstractions"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::crypto_abstractions())
        );
    }
    pub mod dummy_hax_concrete_ident_wrapper {
        #![doc = r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper`]."##]
        pub use super::root;
        pub mod ___1 {
            #![doc = r##"This is the const [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1`]."##]
            pub use super::root;
            mk!(
                Use,
                r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1::Use`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},1],["Use",0]],"Use"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1()
                )
            );
            mk!(
                f,
                r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1::f`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},1],[{"ValueNs":"f"},0]],"Fn"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1()
                )
            );
        }
        pub mod _anonymous {
            #![doc = r##"This is the const [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous`]."##]
            pub use super::root;
            mk!(
                Use,
                r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous::Use`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},0],["Use",0]],"Use"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous()
                )
            );
            mk!(
                Use__1,
                r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous::Use__1`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},0],["Use",1]],"Use"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous()
                )
            );
            mk!(
                Use__2,
                r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous::Use__2`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},0],["Use",2]],"Use"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous()
                )
            );
            mk!(
                arith,
                r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous::arith`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},0],[{"ValueNs":"arith"},0]],"Fn"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous()
                )
            );
        }
        pub mod props {
            #![doc = r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::props`]."##]
            pub use super::root;
            mk!(
                Use,
                r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::props::Use`]."##,
                r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"props"},0],["Use",0]],"Use"]"##,
                ::core::option::Option::Some(
                    root::hax_engine_names::dummy_hax_concrete_ident_wrapper::props()
                )
            );
        }
        mk!(
            Use,
            r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::Use`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],["Use",0]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            Use__1,
            r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::Use__1`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],["Use",1]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            Use__2,
            r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::Use__2`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],["Use",2]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            Use__3,
            r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::Use__3`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],["Use",3]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            Use__4,
            r##"This is the use item [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::Use__4`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],["Use",4]],"Use"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            ___1,
            r##"This is the const [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::___1`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},1]],"Const"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            _anonymous,
            r##"This is the const [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::_anonymous`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"_"},0]],"Const"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            dummy,
            r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::dummy`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"dummy"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            iterator_functions,
            r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::iterator_functions`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"iterator_functions"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            props,
            r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::props`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"props"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            question_mark_result,
            r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::question_mark_result`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"question_mark_result"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
        mk!(
            refinements,
            r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper::refinements`]."##,
            r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0],[{"ValueNs":"refinements"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::dummy_hax_concrete_ident_wrapper())
        );
    }
    pub mod hax {
        #![doc = r##"This is the module [`::hax_engine_names::hax`]."##]
        pub use super::root;
        pub mod Tuple2 {
            #![doc = r##"This is the struct [`::hax_engine_names::hax::Tuple2`]."##]
            pub use super::root;
            mk!(
                _0,
                r##"This is the field [`_0`] from ::hax_engine_names::hax::Tuple2."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0],[{"ValueNs":"0"},0]],"Field"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::Tuple2())
            );
            mk!(
                _1,
                r##"This is the field [`_1`] from ::hax_engine_names::hax::Tuple2."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0],[{"ValueNs":"1"},0]],"Field"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::Tuple2())
            );
        }
        pub mod control_flow_monad {
            #![doc = r##"This is the module [`::hax_engine_names::hax::control_flow_monad`]."##]
            pub use super::root;
            pub mod mexception {
                #![doc = r##"This is the module [`::hax_engine_names::hax::control_flow_monad::mexception`]."##]
                pub use super::root;
                mk!(
                    run,
                    r##"This is the function [`::hax_engine_names::hax::control_flow_monad::mexception::run`]."##,
                    r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"mexception"},0],[{"ValueNs":"run"},0]],"Fn"]"##,
                    ::core::option::Option::Some(
                        root::hax_engine_names::hax::control_flow_monad::mexception()
                    )
                );
            }
            pub mod moption {
                #![doc = r##"This is the module [`::hax_engine_names::hax::control_flow_monad::moption`]."##]
                pub use super::root;
                mk!(
                    run,
                    r##"This is the function [`::hax_engine_names::hax::control_flow_monad::moption::run`]."##,
                    r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"moption"},0],[{"ValueNs":"run"},0]],"Fn"]"##,
                    ::core::option::Option::Some(
                        root::hax_engine_names::hax::control_flow_monad::moption()
                    )
                );
            }
            pub mod mresult {
                #![doc = r##"This is the module [`::hax_engine_names::hax::control_flow_monad::mresult`]."##]
                pub use super::root;
                mk!(
                    run,
                    r##"This is the function [`::hax_engine_names::hax::control_flow_monad::mresult::run`]."##,
                    r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"mresult"},0],[{"ValueNs":"run"},0]],"Fn"]"##,
                    ::core::option::Option::Some(
                        root::hax_engine_names::hax::control_flow_monad::mresult()
                    )
                );
            }
            mk!(
                ControlFlowMonad,
                r##"This is the trait [`::hax_engine_names::hax::control_flow_monad::ControlFlowMonad`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"ControlFlowMonad"},0]],"Trait"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::control_flow_monad())
            );
            mk!(
                mexception,
                r##"This is the module [`::hax_engine_names::hax::control_flow_monad::mexception`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"mexception"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::control_flow_monad())
            );
            mk!(
                moption,
                r##"This is the module [`::hax_engine_names::hax::control_flow_monad::moption`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"moption"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::control_flow_monad())
            );
            mk!(
                mresult,
                r##"This is the module [`::hax_engine_names::hax::control_flow_monad::mresult`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0],[{"TypeNs":"mresult"},0]],"Mod"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::control_flow_monad())
            );
        }
        pub mod folds {
            #![doc = r##"This is the module [`::hax_engine_names::hax::folds`]."##]
            pub use super::root;
            mk!(
                fold_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_chunked_slice,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_chunked_slice`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_chunked_slice"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_chunked_slice_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_chunked_slice_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_chunked_slice_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_chunked_slice_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_chunked_slice_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_chunked_slice_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_chunked_slice,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_chunked_slice`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_chunked_slice"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_chunked_slice_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_chunked_slice_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_chunked_slice_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_chunked_slice_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_chunked_slice_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_chunked_slice_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_slice,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_slice`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_slice"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_slice_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_slice_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_slice_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_enumerated_slice_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_enumerated_slice_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_enumerated_slice_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range_step_by,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range_step_by`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range_step_by"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range_step_by_cf,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range_step_by_cf`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range_step_by_cf"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_range_step_by_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_range_step_by_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_range_step_by_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
            mk!(
                fold_return,
                r##"This is the function [`::hax_engine_names::hax::folds::fold_return`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0],[{"ValueNs":"fold_return"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::folds())
            );
        }
        pub mod int {
            #![doc = r##"This is the module [`::hax_engine_names::hax::int`]."##]
            pub use super::root;
            mk!(
                add,
                r##"This is the function [`::hax_engine_names::hax::int::add`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                div,
                r##"This is the function [`::hax_engine_names::hax::int::div`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                eq,
                r##"This is the function [`::hax_engine_names::hax::int::eq`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                from_machine,
                r##"This is the function [`::hax_engine_names::hax::int::from_machine`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"from_machine"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                ge,
                r##"This is the function [`::hax_engine_names::hax::int::ge`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                gt,
                r##"This is the function [`::hax_engine_names::hax::int::gt`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                into_machine,
                r##"This is the function [`::hax_engine_names::hax::int::into_machine`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"into_machine"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                le,
                r##"This is the function [`::hax_engine_names::hax::int::le`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                lt,
                r##"This is the function [`::hax_engine_names::hax::int::lt`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                mul,
                r##"This is the function [`::hax_engine_names::hax::int::mul`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                ne,
                r##"This is the function [`::hax_engine_names::hax::int::ne`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                neg,
                r##"This is the function [`::hax_engine_names::hax::int::neg`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                rem,
                r##"This is the function [`::hax_engine_names::hax::int::rem`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                sub,
                r##"This is the function [`::hax_engine_names::hax::int::sub`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
        }
        pub mod machine_int {
            #![doc = r##"This is the module [`::hax_engine_names::hax::machine_int`]."##]
            pub use super::root;
            mk!(
                add,
                r##"This is the function [`::hax_engine_names::hax::machine_int::add`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                bitand,
                r##"This is the function [`::hax_engine_names::hax::machine_int::bitand`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"bitand"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                bitor,
                r##"This is the function [`::hax_engine_names::hax::machine_int::bitor`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"bitor"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                bitxor,
                r##"This is the function [`::hax_engine_names::hax::machine_int::bitxor`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"bitxor"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                div,
                r##"This is the function [`::hax_engine_names::hax::machine_int::div`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                eq,
                r##"This is the function [`::hax_engine_names::hax::machine_int::eq`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                ge,
                r##"This is the function [`::hax_engine_names::hax::machine_int::ge`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                gt,
                r##"This is the function [`::hax_engine_names::hax::machine_int::gt`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                le,
                r##"This is the function [`::hax_engine_names::hax::machine_int::le`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                lt,
                r##"This is the function [`::hax_engine_names::hax::machine_int::lt`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                mul,
                r##"This is the function [`::hax_engine_names::hax::machine_int::mul`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                ne,
                r##"This is the function [`::hax_engine_names::hax::machine_int::ne`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                not,
                r##"This is the function [`::hax_engine_names::hax::machine_int::not`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"not"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                rem,
                r##"This is the function [`::hax_engine_names::hax::machine_int::rem`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                shl,
                r##"This is the function [`::hax_engine_names::hax::machine_int::shl`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                shr,
                r##"This is the function [`::hax_engine_names::hax::machine_int::shr`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                sub,
                r##"This is the function [`::hax_engine_names::hax::machine_int::sub`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
        }
        pub mod monomorphized_update_at {
            #![doc = r##"This is the module [`::hax_engine_names::hax::monomorphized_update_at`]."##]
            pub use super::root;
            mk!(
                update_at_range,
                r##"This is the function [`::hax_engine_names::hax::monomorphized_update_at::update_at_range`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_range"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
            mk!(
                update_at_range_from,
                r##"This is the function [`::hax_engine_names::hax::monomorphized_update_at::update_at_range_from`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_range_from"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
            mk!(
                update_at_range_full,
                r##"This is the function [`::hax_engine_names::hax::monomorphized_update_at::update_at_range_full`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_range_full"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
            mk!(
                update_at_range_to,
                r##"This is the function [`::hax_engine_names::hax::monomorphized_update_at::update_at_range_to`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_range_to"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
            mk!(
                update_at_usize,
                r##"This is the function [`::hax_engine_names::hax::monomorphized_update_at::update_at_usize`]."##,
                r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_usize"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
        }
        mk!(
            Failure,
            r##"This is the struct [`::hax_engine_names::hax::Failure`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Failure"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            MutRef,
            r##"This is the enum [`::hax_engine_names::hax::MutRef`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"MutRef"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Never,
            r##"This is the enum [`::hax_engine_names::hax::Never`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Never"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Tuple0,
            r##"This is the struct [`::hax_engine_names::hax::Tuple0`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple0"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Tuple2,
            r##"This is the struct [`::hax_engine_names::hax::Tuple2`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            array_of_list,
            r##"This is the function [`::hax_engine_names::hax::array_of_list`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"array_of_list"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            box_new,
            r##"This is the function [`::hax_engine_names::hax::box_new`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"box_new"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            cast_op,
            r##"This is the function [`::hax_engine_names::hax::cast_op`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"cast_op"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            control_flow_monad,
            r##"This is the module [`::hax_engine_names::hax::control_flow_monad`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"control_flow_monad"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            deref_op,
            r##"This is the function [`::hax_engine_names::hax::deref_op`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"deref_op"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            dropped_body,
            r##"This is the function [`::hax_engine_names::hax::dropped_body`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"dropped_body"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            failure,
            r##"This is the function [`::hax_engine_names::hax::failure`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"failure"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            folds,
            r##"This is the module [`::hax_engine_names::hax::folds`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"folds"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            int,
            r##"This is the module [`::hax_engine_names::hax::int`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            logical_op_and,
            r##"This is the function [`::hax_engine_names::hax::logical_op_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"logical_op_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            logical_op_or,
            r##"This is the function [`::hax_engine_names::hax::logical_op_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"logical_op_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            machine_int,
            r##"This is the module [`::hax_engine_names::hax::machine_int`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            monomorphized_update_at,
            r##"This is the module [`::hax_engine_names::hax::monomorphized_update_at`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            never_to_any,
            r##"This is the function [`::hax_engine_names::hax::never_to_any`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"never_to_any"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            repeat,
            r##"This is the function [`::hax_engine_names::hax::repeat`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"repeat"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            update_at,
            r##"This is the function [`::hax_engine_names::hax::update_at`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"update_at"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            while_loop,
            r##"This is the function [`::hax_engine_names::hax::while_loop`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"while_loop"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            while_loop_cf,
            r##"This is the function [`::hax_engine_names::hax::while_loop_cf`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"while_loop_cf"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            while_loop_return,
            r##"This is the function [`::hax_engine_names::hax::while_loop_return`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"hax"},0],[{"ValueNs":"while_loop_return"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
    }
    pub mod i128 {
        #![doc = r##"This is the module [`::hax_engine_names::i128`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::i128::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::i128::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::i128::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::i128::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::i128::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::i128::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::i128::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::i128::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::i128::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::i128::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::i128::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::i128::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::i128::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::i128::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::i128::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::i128::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::i128::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i128"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i128())
        );
    }
    pub mod i16 {
        #![doc = r##"This is the module [`::hax_engine_names::i16`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::i16::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::i16::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::i16::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::i16::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::i16::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::i16::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::i16::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::i16::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::i16::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::i16::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::i16::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::i16::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::i16::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::i16::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::i16::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::i16::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::i16::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i16"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i16())
        );
    }
    pub mod i32 {
        #![doc = r##"This is the module [`::hax_engine_names::i32`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::i32::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::i32::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::i32::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::i32::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::i32::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::i32::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::i32::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::i32::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::i32::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::i32::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::i32::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::i32::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::i32::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::i32::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::i32::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::i32::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::i32::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i32"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i32())
        );
    }
    pub mod i64 {
        #![doc = r##"This is the module [`::hax_engine_names::i64`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::i64::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::i64::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::i64::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::i64::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::i64::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::i64::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::i64::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::i64::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::i64::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::i64::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::i64::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::i64::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::i64::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::i64::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::i64::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::i64::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::i64::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i64"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i64())
        );
    }
    pub mod i8 {
        #![doc = r##"This is the module [`::hax_engine_names::i8`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::i8::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::i8::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::i8::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::i8::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::i8::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::i8::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::i8::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::i8::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::i8::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::i8::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::i8::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::i8::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::i8::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::i8::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::i8::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::i8::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::i8::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"i8"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::i8())
        );
    }
    pub mod isize {
        #![doc = r##"This is the module [`::hax_engine_names::isize`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::isize::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::isize::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::isize::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::isize::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::isize::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::isize::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::isize::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::isize::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::isize::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::isize::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::isize::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::isize::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::isize::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::isize::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::isize::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::isize::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::isize::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"isize"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::isize())
        );
    }
    pub mod u128 {
        #![doc = r##"This is the module [`::hax_engine_names::u128`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::u128::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::u128::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::u128::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::u128::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::u128::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::u128::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::u128::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::u128::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::u128::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::u128::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::u128::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::u128::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::u128::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::u128::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::u128::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::u128::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::u128::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u128"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u128())
        );
    }
    pub mod u16 {
        #![doc = r##"This is the module [`::hax_engine_names::u16`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::u16::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::u16::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::u16::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::u16::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::u16::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::u16::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::u16::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::u16::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::u16::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::u16::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::u16::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::u16::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::u16::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::u16::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::u16::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::u16::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::u16::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u16"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u16())
        );
    }
    pub mod u32 {
        #![doc = r##"This is the module [`::hax_engine_names::u32`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::u32::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::u32::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::u32::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::u32::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::u32::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::u32::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::u32::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::u32::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::u32::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::u32::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::u32::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::u32::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::u32::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::u32::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::u32::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::u32::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::u32::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u32"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u32())
        );
    }
    pub mod u64 {
        #![doc = r##"This is the module [`::hax_engine_names::u64`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::u64::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::u64::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::u64::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::u64::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::u64::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::u64::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::u64::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::u64::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::u64::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::u64::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::u64::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::u64::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::u64::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::u64::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::u64::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::u64::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::u64::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u64"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u64())
        );
    }
    pub mod u8 {
        #![doc = r##"This is the module [`::hax_engine_names::u8`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::u8::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::u8::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::u8::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::u8::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::u8::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::u8::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::u8::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::u8::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::u8::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::u8::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::u8::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::u8::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::u8::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::u8::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::u8::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::u8::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::u8::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"u8"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::u8())
        );
    }
    pub mod usize {
        #![doc = r##"This is the module [`::hax_engine_names::usize`]."##]
        pub use super::root;
        mk!(
            add,
            r##"This is the function [`::hax_engine_names::usize::add`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            bit_and,
            r##"This is the function [`::hax_engine_names::usize::bit_and`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"bit_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            bit_or,
            r##"This is the function [`::hax_engine_names::usize::bit_or`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"bit_or"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            bit_xor,
            r##"This is the function [`::hax_engine_names::usize::bit_xor`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"bit_xor"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            div,
            r##"This is the function [`::hax_engine_names::usize::div`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"div"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            eq,
            r##"This is the function [`::hax_engine_names::usize::eq`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            ge,
            r##"This is the function [`::hax_engine_names::usize::ge`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"ge"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            gt,
            r##"This is the function [`::hax_engine_names::usize::gt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"gt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            le,
            r##"This is the function [`::hax_engine_names::usize::le`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"le"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            lt,
            r##"This is the function [`::hax_engine_names::usize::lt`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"lt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            mul,
            r##"This is the function [`::hax_engine_names::usize::mul`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"mul"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            ne,
            r##"This is the function [`::hax_engine_names::usize::ne`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            neg,
            r##"This is the function [`::hax_engine_names::usize::neg`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"neg"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            rem,
            r##"This is the function [`::hax_engine_names::usize::rem`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"rem"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            shl,
            r##"This is the function [`::hax_engine_names::usize::shl`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"shl"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            shr,
            r##"This is the function [`::hax_engine_names::usize::shr`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"shr"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
        mk!(
            sub,
            r##"This is the function [`::hax_engine_names::usize::sub`]."##,
            r##"["hax_engine_names",[[{"TypeNs":"usize"},0],[{"ValueNs":"sub"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::usize())
        );
    }
    mk!(
        Use,
        r##"This is the use item [`::hax_engine_names::Use`]."##,
        r##"["hax_engine_names",[["Use",0]],"Use"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        alloc,
        r##"This is the extern crate [`::hax_engine_names::alloc`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"alloc"},0]],"ExternCrate"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        crypto_abstractions,
        r##"This is the module [`::hax_engine_names::crypto_abstractions`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"crypto_abstractions"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        dummy_hax_concrete_ident_wrapper,
        r##"This is the function [`::hax_engine_names::dummy_hax_concrete_ident_wrapper`]."##,
        r##"["hax_engine_names",[[{"ValueNs":"dummy_hax_concrete_ident_wrapper"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        hax,
        r##"This is the module [`::hax_engine_names::hax`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"hax"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        i128,
        r##"This is the module [`::hax_engine_names::i128`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"i128"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        i16,
        r##"This is the module [`::hax_engine_names::i16`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"i16"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        i32,
        r##"This is the module [`::hax_engine_names::i32`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"i32"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        i64,
        r##"This is the module [`::hax_engine_names::i64`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"i64"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        i8,
        r##"This is the module [`::hax_engine_names::i8`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"i8"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        impl_arith,
        r##"This is the macro [`::hax_engine_names::impl_arith`]."##,
        r##"["hax_engine_names",[[{"MacroNs":"impl_arith"},0]],{"Macro":"Bang"}]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        isize,
        r##"This is the module [`::hax_engine_names::isize`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"isize"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        offset,
        r##"This is the function [`::hax_engine_names::offset`]."##,
        r##"["hax_engine_names",[[{"ValueNs":"offset"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        std,
        r##"This is the extern crate [`::hax_engine_names::std`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"std"},0]],"ExternCrate"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        u128,
        r##"This is the module [`::hax_engine_names::u128`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"u128"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        u16,
        r##"This is the module [`::hax_engine_names::u16`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"u16"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        u32,
        r##"This is the module [`::hax_engine_names::u32`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"u32"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        u64,
        r##"This is the module [`::hax_engine_names::u64`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"u64"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        u8,
        r##"This is the module [`::hax_engine_names::u8`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"u8"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        unsize,
        r##"This is the function [`::hax_engine_names::unsize`]."##,
        r##"["hax_engine_names",[[{"ValueNs":"unsize"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
    mk!(
        usize,
        r##"This is the module [`::hax_engine_names::usize`]."##,
        r##"["hax_engine_names",[[{"TypeNs":"usize"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
}
pub mod hax_lib {
    #![doc = r##"This is the module [`::hax_lib`]."##]
    pub use super::root;
    pub mod int {
        #![doc = r##"This is the module [`::hax_lib::int`]."##]
        pub use super::root;
        pub mod Impl__7 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                _unsafe_from_str,
                r##"This is the associated function [`::hax_lib::int::Impl__7::_unsafe_from_str`]."##,
                r##"["hax_lib",[[{"TypeNs":"int"},0],["Impl",7],[{"ValueNs":"_unsafe_from_str"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib::int::Impl__7())
            );
            mk!(
                pow2,
                r##"This is the associated function [`::hax_lib::int::Impl__7::pow2`]."##,
                r##"["hax_lib",[[{"TypeNs":"int"},0],["Impl",7],[{"ValueNs":"pow2"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib::int::Impl__7())
            );
        }
        mk!(
            Impl__7,
            r##"This is a impl block."##,
            r##"["hax_lib",[[{"TypeNs":"int"},0],["Impl",7]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib::int())
        );
        mk!(
            Impl__9,
            r##"This is a impl block."##,
            r##"["hax_lib",[[{"TypeNs":"int"},0],["Impl",9]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::hax_lib::int())
        );
        mk!(
            Int,
            r##"This is the struct [`::hax_lib::int::Int`]."##,
            r##"["hax_lib",[[{"TypeNs":"int"},0],[{"TypeNs":"Int"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib::int())
        );
    }
    pub mod prop {
        #![doc = r##"This is the module [`::hax_lib::prop`]."##]
        pub use super::root;
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bool,
                r##"This is the associated function [`::hax_lib::prop::Impl::from_bool`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],["Impl",0],[{"ValueNs":"from_bool"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::Impl())
            );
        }
        pub mod constructors {
            #![doc = r##"This is the module [`::hax_lib::prop::constructors`]."##]
            pub use super::root;
            mk!(
                and,
                r##"This is the function [`::hax_lib::prop::constructors::and`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"and"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                eq,
                r##"This is the function [`::hax_lib::prop::constructors::eq`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                exists,
                r##"This is the function [`::hax_lib::prop::constructors::exists`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"exists"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                forall,
                r##"This is the function [`::hax_lib::prop::constructors::forall`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"forall"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                from_bool,
                r##"This is the function [`::hax_lib::prop::constructors::from_bool`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"from_bool"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                implies,
                r##"This is the function [`::hax_lib::prop::constructors::implies`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"implies"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                ne,
                r##"This is the function [`::hax_lib::prop::constructors::ne`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"ne"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                not,
                r##"This is the function [`::hax_lib::prop::constructors::not`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"not"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
            mk!(
                or,
                r##"This is the function [`::hax_lib::prop::constructors::or`]."##,
                r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0],[{"ValueNs":"or"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_lib::prop::constructors())
            );
        }
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["hax_lib",[[{"TypeNs":"prop"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib::prop())
        );
        mk!(
            Impl__3,
            r##"This is a impl block."##,
            r##"["hax_lib",[[{"TypeNs":"prop"},0],["Impl",3]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::hax_lib::prop())
        );
        mk!(
            Prop,
            r##"This is the struct [`::hax_lib::prop::Prop`]."##,
            r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"Prop"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib::prop())
        );
        mk!(
            constructors,
            r##"This is the module [`::hax_lib::prop::constructors`]."##,
            r##"["hax_lib",[[{"TypeNs":"prop"},0],[{"TypeNs":"constructors"},0]],"Mod"]"##,
            ::core::option::Option::Some(root::hax_lib::prop())
        );
    }
    mk!(
        RefineAs,
        r##"This is the trait [`::hax_lib::RefineAs`]."##,
        r##"["hax_lib",[[{"TypeNs":"RefineAs"},0]],"Trait"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        Refinement,
        r##"This is the trait [`::hax_lib::Refinement`]."##,
        r##"["hax_lib",[[{"TypeNs":"Refinement"},0]],"Trait"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        _internal_loop_decreases,
        r##"This is the function [`::hax_lib::_internal_loop_decreases`]."##,
        r##"["hax_lib",[[{"ValueNs":"_internal_loop_decreases"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        _internal_loop_invariant,
        r##"This is the function [`::hax_lib::_internal_loop_invariant`]."##,
        r##"["hax_lib",[[{"ValueNs":"_internal_loop_invariant"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        _internal_while_loop_invariant,
        r##"This is the function [`::hax_lib::_internal_while_loop_invariant`]."##,
        r##"["hax_lib",[[{"ValueNs":"_internal_while_loop_invariant"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        any_to_unit,
        r##"This is the function [`::hax_lib::any_to_unit`]."##,
        r##"["hax_lib",[[{"ValueNs":"any_to_unit"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        assert,
        r##"This is the function [`::hax_lib::assert`]."##,
        r##"["hax_lib",[[{"ValueNs":"assert"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        int,
        r##"This is the module [`::hax_lib::int`]."##,
        r##"["hax_lib",[[{"TypeNs":"int"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
    mk!(
        prop,
        r##"This is the module [`::hax_lib::prop`]."##,
        r##"["hax_lib",[[{"TypeNs":"prop"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_lib())
    );
}
pub mod hax_lib_protocol {
    #![doc = r##"This is the module [`::hax_lib_protocol`]."##]
    pub use super::root;
    pub mod crypto {
        #![doc = r##"This is the module [`::hax_lib_protocol::crypto`]."##]
        pub use super::root;
        pub mod AEADAlgorithm {
            #![doc = r##"This is the enum [`::hax_lib_protocol::crypto::AEADAlgorithm`]."##]
            pub use super::root;
            mk!(
                Chacha20Poly1305,
                r##"This is the variant [`::hax_lib_protocol::crypto::AEADAlgorithm::Chacha20Poly1305`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"AEADAlgorithm"},0],[{"TypeNs":"Chacha20Poly1305"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::AEADAlgorithm())
            );
        }
        pub mod DHGroup {
            #![doc = r##"This is the enum [`::hax_lib_protocol::crypto::DHGroup`]."##]
            pub use super::root;
            mk!(
                X25519,
                r##"This is the variant [`::hax_lib_protocol::crypto::DHGroup::X25519`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"DHGroup"},0],[{"TypeNs":"X25519"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::DHGroup())
            );
        }
        pub mod HMACAlgorithm {
            #![doc = r##"This is the enum [`::hax_lib_protocol::crypto::HMACAlgorithm`]."##]
            pub use super::root;
            mk!(
                Sha256,
                r##"This is the variant [`::hax_lib_protocol::crypto::HMACAlgorithm::Sha256`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"HMACAlgorithm"},0],[{"TypeNs":"Sha256"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::HMACAlgorithm())
            );
        }
        pub mod HashAlgorithm {
            #![doc = r##"This is the enum [`::hax_lib_protocol::crypto::HashAlgorithm`]."##]
            pub use super::root;
            mk!(
                Sha256,
                r##"This is the variant [`::hax_lib_protocol::crypto::HashAlgorithm::Sha256`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"HashAlgorithm"},0],[{"TypeNs":"Sha256"},0]],"Variant"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::HashAlgorithm())
            );
        }
        pub mod Impl {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bytes,
                r##"This is the associated function [`::hax_lib_protocol::crypto::Impl::from_bytes`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",0],[{"ValueNs":"from_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::Impl())
            );
        }
        pub mod Impl__1 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bytes,
                r##"This is the associated function [`::hax_lib_protocol::crypto::Impl__1::from_bytes`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",1],[{"ValueNs":"from_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::Impl__1())
            );
        }
        pub mod Impl__4 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bytes,
                r##"This is the associated function [`::hax_lib_protocol::crypto::Impl__4::from_bytes`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",4],[{"ValueNs":"from_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::Impl__4())
            );
        }
        pub mod Impl__5 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bytes,
                r##"This is the associated function [`::hax_lib_protocol::crypto::Impl__5::from_bytes`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",5],[{"ValueNs":"from_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::Impl__5())
            );
        }
        pub mod Impl__6 {
            #![doc = r##"This is a impl block."##]
            pub use super::root;
            mk!(
                from_bytes,
                r##"This is the associated function [`::hax_lib_protocol::crypto::Impl__6::from_bytes`]."##,
                r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",6],[{"ValueNs":"from_bytes"},0]],"AssocFn"]"##,
                ::core::option::Option::Some(root::hax_lib_protocol::crypto::Impl__6())
            );
        }
        mk!(
            AEADAlgorithm,
            r##"This is the enum [`::hax_lib_protocol::crypto::AEADAlgorithm`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"AEADAlgorithm"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            AEADIV,
            r##"This is the struct [`::hax_lib_protocol::crypto::AEADIV`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"AEADIV"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            AEADKey,
            r##"This is the struct [`::hax_lib_protocol::crypto::AEADKey`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"AEADKey"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            AEADTag,
            r##"This is the struct [`::hax_lib_protocol::crypto::AEADTag`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"AEADTag"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            DHElement,
            r##"This is the struct [`::hax_lib_protocol::crypto::DHElement`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"DHElement"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            DHGroup,
            r##"This is the enum [`::hax_lib_protocol::crypto::DHGroup`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"DHGroup"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            DHScalar,
            r##"This is the struct [`::hax_lib_protocol::crypto::DHScalar`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"DHScalar"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            HMACAlgorithm,
            r##"This is the enum [`::hax_lib_protocol::crypto::HMACAlgorithm`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"HMACAlgorithm"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            HashAlgorithm,
            r##"This is the enum [`::hax_lib_protocol::crypto::HashAlgorithm`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"TypeNs":"HashAlgorithm"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",0]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl__1,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",1]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl__4,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",4]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl__5,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",5]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl__6,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",6]],{"Impl":{"of_trait":false}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            Impl__9,
            r##"This is a impl block."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],["Impl",9]],{"Impl":{"of_trait":true}}]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            aead_decrypt,
            r##"This is the function [`::hax_lib_protocol::crypto::aead_decrypt`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"aead_decrypt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            aead_encrypt,
            r##"This is the function [`::hax_lib_protocol::crypto::aead_encrypt`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"aead_encrypt"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            dh_scalar_multiply,
            r##"This is the function [`::hax_lib_protocol::crypto::dh_scalar_multiply`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"dh_scalar_multiply"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            dh_scalar_multiply_base,
            r##"This is the function [`::hax_lib_protocol::crypto::dh_scalar_multiply_base`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"dh_scalar_multiply_base"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            hash,
            r##"This is the function [`::hax_lib_protocol::crypto::hash`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"hash"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
        mk!(
            hmac,
            r##"This is the function [`::hax_lib_protocol::crypto::hmac`]."##,
            r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0],[{"ValueNs":"hmac"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_lib_protocol::crypto())
        );
    }
    mk!(
        ProtocolError,
        r##"This is the enum [`::hax_lib_protocol::ProtocolError`]."##,
        r##"["hax_lib_protocol",[[{"TypeNs":"ProtocolError"},0]],"Enum"]"##,
        ::core::option::Option::Some(root::hax_lib_protocol())
    );
    mk!(
        crypto,
        r##"This is the module [`::hax_lib_protocol::crypto`]."##,
        r##"["hax_lib_protocol",[[{"TypeNs":"crypto"},0]],"Mod"]"##,
        ::core::option::Option::Some(root::hax_lib_protocol())
    );
}
pub mod rust_primitives {
    pub use super::root;
    pub mod hax {
        pub use super::root;
        pub mod Tuple0 {
            #![doc = r##"This is the struct [`::rust_primitives::hax::Tuple0`]."##]
            pub use super::root;
            mk!(
                Tuple1,
                r##"This is the field [`Tuple1`] from ::rust_primitives::hax::Tuple0."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple0"},0],[{"ValueNs":"Tuple1"},0]],"Field"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::Tuple0())
            );
            mk!(
                ctor,
                r##"This is the constructor for [`::rust_primitives::hax::Tuple0`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple0"},0]],{"Ctor":["Struct","Fn"]}]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax())
            );
        }
        pub mod Tuple2 {
            #![doc = r##"This is the struct [`::rust_primitives::hax::Tuple2`]."##]
            pub use super::root;
            mk!(
                Tuple0,
                r##"This is the field [`Tuple0`] from ::rust_primitives::hax::Tuple2."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0],[{"ValueNs":"Tuple0"},0]],"Field"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::Tuple2())
            );
            mk!(
                Tuple1,
                r##"This is the field [`Tuple1`] from ::rust_primitives::hax::Tuple2."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0],[{"ValueNs":"Tuple1"},0]],"Field"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::Tuple2())
            );
            mk!(
                ctor,
                r##"This is the constructor for [`::rust_primitives::hax::Tuple2`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0]],{"Ctor":["Struct","Fn"]}]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax())
            );
        }
        pub mod int {
            pub use super::root;
            mk!(
                from_machine,
                r##"This is the function [`::rust_primitives::hax::int::from_machine`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"from_machine"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
            mk!(
                into_machine,
                r##"This is the function [`::rust_primitives::hax::int::into_machine`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"int"},0],[{"ValueNs":"into_machine"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::int())
            );
        }
        pub mod machine_int {
            pub use super::root;
            mk!(
                add,
                r##"This is the function [`::rust_primitives::hax::machine_int::add`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"add"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
            mk!(
                eq,
                r##"This is the function [`::rust_primitives::hax::machine_int::eq`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"machine_int"},0],[{"ValueNs":"eq"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::machine_int())
            );
        }
        pub mod monomorphized_update_at {
            pub use super::root;
            mk!(
                update_at_usize,
                r##"This is the function [`::rust_primitives::hax::monomorphized_update_at::update_at_usize`]."##,
                r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"monomorphized_update_at"},0],[{"ValueNs":"update_at_usize"},0]],"Fn"]"##,
                ::core::option::Option::Some(root::hax_engine_names::hax::monomorphized_update_at())
            );
        }
        mk!(
            Never,
            r##"This is the enum [`::rust_primitives::hax::Never`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Never"},0]],"Enum"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Tuple0,
            r##"This is the struct [`::rust_primitives::hax::Tuple0`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple0"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Tuple1,
            r##"This is the struct [`::rust_primitives::hax::Tuple1`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple1"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            Tuple2,
            r##"This is the struct [`::rust_primitives::hax::Tuple2`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"TypeNs":"Tuple2"},0]],"Struct"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            box_new,
            r##"This is the function [`::rust_primitives::hax::box_new`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"ValueNs":"box_new"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            failure,
            r##"This is the function [`::rust_primitives::hax::failure`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"ValueNs":"failure"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
        mk!(
            logical_op_and,
            r##"This is the function [`::rust_primitives::hax::logical_op_and`]."##,
            r##"["rust_primitives",[[{"TypeNs":"hax"},0],[{"ValueNs":"logical_op_and"},0]],"Fn"]"##,
            ::core::option::Option::Some(root::hax_engine_names::hax())
        );
    }
    mk!(
        unsize,
        r##"This is the function [`::rust_primitives::unsize`]."##,
        r##"["rust_primitives",[[{"ValueNs":"unsize"},0]],"Fn"]"##,
        ::core::option::Option::Some(root::hax_engine_names())
    );
}
mk!(
    alloc,
    r##"This is the module [`::alloc`]."##,
    r##"["alloc",[],"Mod"]"##,
    ::core::option::Option::None
);
mk!(
    core,
    r##"This is the module [`::core`]."##,
    r##"["core",[],"Mod"]"##,
    ::core::option::Option::None
);
mk!(
    hax_engine_names,
    r##"This is the module [`::hax_engine_names`]."##,
    r##"["hax_engine_names",[],"Mod"]"##,
    ::core::option::Option::None
);
mk!(
    hax_lib,
    r##"This is the module [`::hax_lib`]."##,
    r##"["hax_lib",[],"Mod"]"##,
    ::core::option::Option::None
);
mk!(
    hax_lib_protocol,
    r##"This is the module [`::hax_lib_protocol`]."##,
    r##"["hax_lib_protocol",[],"Mod"]"##,
    ::core::option::Option::None
);
