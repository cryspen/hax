# hax proc macros

Hax-specific proc-macros for Rust programs.

This crate defines proc macros to be used in Rust programs that are extracted with hax.
It provides proc macros such as `requires` and `ensures` to define pre- and post-conditions for functions.

## How the macros communicate with the engine

The hax engine understands only one attribute: `#[_hax::json(PAYLOAD)]`, where `PAYLOAD` is a JSON serialization of the Rust enum `hax_lib_macros_types::AttrPayload`.
The crate `hax-lib-macros-types` lives in `hax-lib/macros/types/`.

Note `#[_hax::json(PAYLOAD)]` is a [tool attribute](https://github.com/rust-lang/rust/issues/66079): an attribute that is never expanded.

Asking the user to type `#[_hax::json(some_long_json)]` is not very friendly.
Thus, this crate defines a bunch of [proc macros](https://doc.rust-lang.org/beta/reference/procedural-macros.html) that provide nice and simple-to-use macros.
Those macros take care of cooking some `hax_lib_macros_types::AttrPayload` payload(s), then serialize those payloads to JSON and produce one or more `#[_hax::json(serialized_payload)]` attributes.

In the engine, the OCaml module `Attr_payloads` offers an API to query attributes easily.
The types in crate `hax-lib-macros-types` and corresponding serializers/deserializers are automatically generated in OCaml, thus there is no manual parsing involved.
