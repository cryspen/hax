#[allow(unused)]
#[allow(non_snake_case)]
pub mod root {
    pub mod prelude {
        pub use hax_rust_engine::ast::global_id::DefId;
        pub use std::sync::LazyLock;
    }
    use super::root;
    use root::prelude::*;
    pub mod literals {
        use super::root;
        use root::prelude::*;
        pub mod Foo {
            use super::root;
            use root::prelude::*;

            pub fn field() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["literals",[{"data":{"TypeNs":"Foo"},"disambiguator":0},{"data":{"ValueNs":"field"},"disambiguator":0}],"Field"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::literals::Foo())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod _anonymous {
            use super::root;
            use root::prelude::*;

            pub fn Use() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["literals",[{"data":{"ValueNs":"_"},"disambiguator":0},{"data":"Use","disambiguator":0}],"Use"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::literals::_anonymous())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Use__1() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["literals",[{"data":{"ValueNs":"_"},"disambiguator":0},{"data":"Use","disambiguator":1}],"Use"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::literals::_anonymous())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Use__2() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["literals",[{"data":{"ValueNs":"_"},"disambiguator":0},{"data":"Use","disambiguator":2}],"Use"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::literals::_anonymous())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn requires() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["literals",[{"data":{"ValueNs":"_"},"disambiguator":0},{"data":{"ValueNs":"requires"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::literals::_anonymous())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }

        pub fn Impl() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":"Impl","disambiguator":0}],{"Impl":{"of_trait":true}}]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn Impl__1() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":"Impl","disambiguator":1}],{"Impl":{"of_trait":true}}]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn Impl__2() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":"Impl","disambiguator":2}],{"Impl":{"of_trait":true}}]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn Use() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":"Use","disambiguator":0}],"Use"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn Use__1() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":"Use","disambiguator":1}],"Use"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn Foo() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"TypeNs":"Foo"},"disambiguator":0}],"Struct"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn std() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"TypeNs":"std"},"disambiguator":0}],"ExternCrate"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn CONSTANT() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"ValueNs":"CONSTANT"},"disambiguator":0}],"Const"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn _anonymous() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"ValueNs":"_"},"disambiguator":0}],"Const"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn casts() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"ValueNs":"casts"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn empty_array() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"ValueNs":"empty_array"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn fn_pointer_cast() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"ValueNs":"fn_pointer_cast"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn math_integers() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"ValueNs":"math_integers"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn null() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"ValueNs":"null"},"disambiguator":0}],"Const"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn numeric() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"ValueNs":"numeric"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn panic_with_msg() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["literals",[{"data":{"ValueNs":"panic_with_msg"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn patterns() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["literals",[{"data":{"ValueNs":"patterns"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::literals())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }
    }
    pub mod rust_primitives {
        use super::root;
        use root::prelude::*;
        pub mod hax {
            use super::root;
            use root::prelude::*;
            pub mod Tuple0 {
                use super::root;
                use root::prelude::*;

                pub fn ctor() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple0"},"disambiguator":0}],{"Ctor":["Struct","Fn"]}]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_engine_names::hax())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Tuple2 {
                use super::root;
                use root::prelude::*;

                pub fn ctor() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple2"},"disambiguator":0}],{"Ctor":["Struct","Fn"]}]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_engine_names::hax())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn Tuple0() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple2"},"disambiguator":0},{"data":{"ValueNs":"Tuple0"},"disambiguator":0}],"Field"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_engine_names::hax::Tuple2())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn Tuple1() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple2"},"disambiguator":0},{"data":{"ValueNs":"Tuple1"},"disambiguator":0}],"Field"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_engine_names::hax::Tuple2())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn Never() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Never"},"disambiguator":0}],"Enum"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Tuple0() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple0"},"disambiguator":0}],"Struct"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Tuple2() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple2"},"disambiguator":0}],"Struct"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn cast_op() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"ValueNs":"cast_op"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn deref_op() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"ValueNs":"deref_op"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn logical_op_and() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"ValueNs":"logical_op_and"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn never_to_any() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["rust_primitives",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"ValueNs":"never_to_any"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }

        pub fn unsize() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["rust_primitives",[{"data":{"ValueNs":"unsize"},"disambiguator":0}],"Fn"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::hax_engine_names())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }
    }
    pub mod hax_engine_names {
        use super::root;
        use root::prelude::*;
        pub mod hax {
            use super::root;
            use root::prelude::*;

            pub fn Tuple2() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_engine_names",[{"data":{"TypeNs":"hax"},"disambiguator":0},{"data":{"TypeNs":"Tuple2"},"disambiguator":0}],"Struct"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_engine_names::hax())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }

        pub fn hax() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["hax_engine_names",[{"data":{"TypeNs":"hax"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::hax_engine_names())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }
    }
    pub mod core {
        use super::root;
        use root::prelude::*;
        pub mod cmp {
            use super::root;
            use root::prelude::*;
            pub mod PartialEq {
                use super::root;
                use root::prelude::*;

                pub fn eq() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialEq"},"disambiguator":0},{"data":{"ValueNs":"eq"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialEq())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn ne() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialEq"},"disambiguator":0},{"data":{"ValueNs":"ne"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialEq())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod PartialOrd {
                use super::root;
                use root::prelude::*;

                pub fn ge() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialOrd"},"disambiguator":0},{"data":{"ValueNs":"ge"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialOrd())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn gt() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialOrd"},"disambiguator":0},{"data":{"ValueNs":"gt"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialOrd())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn le() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialOrd"},"disambiguator":0},{"data":{"ValueNs":"le"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialOrd())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn lt() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialOrd"},"disambiguator":0},{"data":{"ValueNs":"lt"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::cmp::PartialOrd())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn Eq() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"Eq"},"disambiguator":0}],"Trait"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::cmp())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn PartialEq() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialEq"},"disambiguator":0}],"Trait"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::cmp())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn PartialOrd() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0},{"data":{"TypeNs":"PartialOrd"},"disambiguator":0}],"Trait"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::cmp())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod ops {
            use super::root;
            use root::prelude::*;
            pub mod arith {
                use super::root;
                use root::prelude::*;
                pub mod Mul {
                    use super::root;
                    use root::prelude::*;

                    pub fn Output() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Mul"},"disambiguator":0},{"data":{"TypeNs":"Output"},"disambiguator":0}],"AssocTy"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Mul())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }

                    pub fn mul() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Mul"},"disambiguator":0},{"data":{"ValueNs":"mul"},"disambiguator":0}],"AssocFn"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Mul())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }
                }
                pub mod Sub {
                    use super::root;
                    use root::prelude::*;

                    pub fn Output() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Sub"},"disambiguator":0},{"data":{"TypeNs":"Output"},"disambiguator":0}],"AssocTy"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Sub())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }

                    pub fn sub() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Sub"},"disambiguator":0},{"data":{"ValueNs":"sub"},"disambiguator":0}],"AssocFn"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Sub())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }
                }
                pub mod Div {
                    use super::root;
                    use root::prelude::*;

                    pub fn Output() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Div"},"disambiguator":0},{"data":{"TypeNs":"Output"},"disambiguator":0}],"AssocTy"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Div())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }

                    pub fn div() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Div"},"disambiguator":0},{"data":{"ValueNs":"div"},"disambiguator":0}],"AssocFn"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Div())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }
                }
                pub mod Add {
                    use super::root;
                    use root::prelude::*;

                    pub fn Output() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Add"},"disambiguator":0},{"data":{"TypeNs":"Output"},"disambiguator":0}],"AssocTy"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Add())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }

                    pub fn add() -> DefId {
                        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                            let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Add"},"disambiguator":0},{"data":{"ValueNs":"add"},"disambiguator":0}],"AssocFn"]"###;
                            let (krate, path, kind) = serde_json::from_str(data).unwrap();
                            DefId {
                                parent: Some(Box::new(root::core::ops::arith::Add())),
                                krate,
                                path,
                                kind,
                            }
                        });
                        (&*DEF_ID).clone()
                    }
                }

                pub fn Add() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Add"},"disambiguator":0}],"Trait"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::ops::arith())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn Div() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Div"},"disambiguator":0}],"Trait"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::ops::arith())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn Mul() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Mul"},"disambiguator":0}],"Trait"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::ops::arith())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn Sub() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0},{"data":{"TypeNs":"Sub"},"disambiguator":0}],"Trait"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::ops::arith())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn arith() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0},{"data":{"TypeNs":"arith"},"disambiguator":0}],"Mod"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::ops())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod panicking {
            use super::root;
            use root::prelude::*;

            pub fn panic_fmt() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"panicking"},"disambiguator":0},{"data":{"ValueNs":"panic_fmt"},"disambiguator":0}],"Fn"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::panicking())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod marker {
            use super::root;
            use root::prelude::*;

            pub fn StructuralPartialEq() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"marker"},"disambiguator":0},{"data":{"TypeNs":"StructuralPartialEq"},"disambiguator":0}],"Trait"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::marker())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod fmt {
            use super::root;
            use root::prelude::*;
            pub mod Impl__4 {
                use super::root;
                use root::prelude::*;

                pub fn new_const() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["core",[{"data":{"TypeNs":"fmt"},"disambiguator":0},{"data":"Impl","disambiguator":4},{"data":{"ValueNs":"new_const"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::core::fmt::Impl__4())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn Impl__4() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"fmt"},"disambiguator":0},{"data":"Impl","disambiguator":4}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::fmt())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Arguments() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["core",[{"data":{"TypeNs":"fmt"},"disambiguator":0},{"data":{"TypeNs":"Arguments"},"disambiguator":0}],"Struct"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::core::fmt())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }

        pub fn cmp() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["core",[{"data":{"TypeNs":"cmp"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::core())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn fmt() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["core",[{"data":{"TypeNs":"fmt"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::core())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn marker() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["core",[{"data":{"TypeNs":"marker"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::core())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn ops() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["core",[{"data":{"TypeNs":"ops"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::core())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn panicking() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data =
                    r###"["core",[{"data":{"TypeNs":"panicking"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::core())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }
    }
    pub mod hax_lib {
        use super::root;
        use root::prelude::*;
        pub mod abstraction {
            use super::root;
            use root::prelude::*;
            pub mod Abstraction {
                use super::root;
                use root::prelude::*;

                pub fn AbstractType() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"abstraction"},"disambiguator":0},{"data":{"TypeNs":"Abstraction"},"disambiguator":0},{"data":{"TypeNs":"AbstractType"},"disambiguator":0}],"AssocTy"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::abstraction::Abstraction())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }

                pub fn lift() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"abstraction"},"disambiguator":0},{"data":{"TypeNs":"Abstraction"},"disambiguator":0},{"data":{"ValueNs":"lift"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::abstraction::Abstraction())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn Abstraction() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"abstraction"},"disambiguator":0},{"data":{"TypeNs":"Abstraction"},"disambiguator":0}],"Trait"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::abstraction())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }
        pub mod int {
            use super::root;
            use root::prelude::*;
            pub mod Impl__7 {
                use super::root;
                use root::prelude::*;

                pub fn _unsafe_from_str() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":7},{"data":{"ValueNs":"_unsafe_from_str"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__7())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__47 {
                use super::root;
                use root::prelude::*;

                pub fn to_u64() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":47},{"data":{"ValueNs":"to_u64"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__47())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__43 {
                use super::root;
                use root::prelude::*;

                pub fn to_u16() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":43},{"data":{"ValueNs":"to_u16"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__43())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__55 {
                use super::root;
                use root::prelude::*;

                pub fn to_i16() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":55},{"data":{"ValueNs":"to_i16"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__55())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__41 {
                use super::root;
                use root::prelude::*;

                pub fn to_u8() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":41},{"data":{"ValueNs":"to_u8"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__41())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__61 {
                use super::root;
                use root::prelude::*;

                pub fn to_i128() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":61},{"data":{"ValueNs":"to_i128"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__61())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__63 {
                use super::root;
                use root::prelude::*;

                pub fn to_isize() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":63},{"data":{"ValueNs":"to_isize"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__63())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__49 {
                use super::root;
                use root::prelude::*;

                pub fn to_u128() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":49},{"data":{"ValueNs":"to_u128"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__49())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__45 {
                use super::root;
                use root::prelude::*;

                pub fn to_u32() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":45},{"data":{"ValueNs":"to_u32"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__45())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__51 {
                use super::root;
                use root::prelude::*;

                pub fn to_usize() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":51},{"data":{"ValueNs":"to_usize"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__51())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__59 {
                use super::root;
                use root::prelude::*;

                pub fn to_i64() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":59},{"data":{"ValueNs":"to_i64"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__59())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }
            pub mod Impl__57 {
                use super::root;
                use root::prelude::*;

                pub fn to_i32() -> DefId {
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                        let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":57},{"data":{"ValueNs":"to_i32"},"disambiguator":0}],"AssocFn"]"###;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {
                            parent: Some(Box::new(root::hax_lib::int::Impl__57())),
                            krate,
                            path,
                            kind,
                        }
                    });
                    (&*DEF_ID).clone()
                }
            }

            pub fn Impl__2() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":2}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__4() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":4}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__5() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":5}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__6() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":6}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__7() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":7}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__12() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":12}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__14() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":14}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__26() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":26}],{"Impl":{"of_trait":true}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__41() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":41}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__43() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":43}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__45() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":45}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__47() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":47}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__49() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":49}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__51() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":51}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__55() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":55}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__57() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":57}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__59() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":59}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__61() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":61}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Impl__63() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":"Impl","disambiguator":63}],{"Impl":{"of_trait":false}}]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }

            pub fn Int() -> DefId {
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0},{"data":{"TypeNs":"Int"},"disambiguator":0}],"Struct"]"###;
                    let (krate, path, kind) = serde_json::from_str(data).unwrap();
                    DefId {
                        parent: Some(Box::new(root::hax_lib::int())),
                        krate,
                        path,
                        kind,
                    }
                });
                (&*DEF_ID).clone()
            }
        }

        pub fn abstraction() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["hax_lib",[{"data":{"TypeNs":"abstraction"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::hax_lib())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }

        pub fn int() -> DefId {
            static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                let data = r###"["hax_lib",[{"data":{"TypeNs":"int"},"disambiguator":0}],"Mod"]"###;
                let (krate, path, kind) = serde_json::from_str(data).unwrap();
                DefId {
                    parent: Some(Box::new(root::hax_lib())),
                    krate,
                    path,
                    kind,
                }
            });
            (&*DEF_ID).clone()
        }
    }

    pub fn core() -> DefId {
        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
            let data = r###"["core",[],"Mod"]"###;
            let (krate, path, kind) = serde_json::from_str(data).unwrap();
            DefId {
                parent: None,
                krate,
                path,
                kind,
            }
        });
        (&*DEF_ID).clone()
    }

    pub fn hax_engine_names() -> DefId {
        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
            let data = r###"["hax_engine_names",[],"Mod"]"###;
            let (krate, path, kind) = serde_json::from_str(data).unwrap();
            DefId {
                parent: None,
                krate,
                path,
                kind,
            }
        });
        (&*DEF_ID).clone()
    }

    pub fn hax_lib() -> DefId {
        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
            let data = r###"["hax_lib",[],"Mod"]"###;
            let (krate, path, kind) = serde_json::from_str(data).unwrap();
            DefId {
                parent: None,
                krate,
                path,
                kind,
            }
        });
        (&*DEF_ID).clone()
    }

    pub fn literals() -> DefId {
        static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
            let data = r###"["literals",[],"Mod"]"###;
            let (krate, path, kind) = serde_json::from_str(data).unwrap();
            DefId {
                parent: None,
                krate,
                path,
                kind,
            }
        });
        (&*DEF_ID).clone()
    }
}
