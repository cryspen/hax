module Rust_primitives.Hax.Control_flow_monad.Moption

let run #a (f: Core_models.Option.t_Option (Core_models.Option.t_Option a)): Core_models.Option.t_Option a
    = match f with
    | Core_models.Option.Option_Some x -> x 
    | Core_models.Option.Option_None -> Core_models.Option.Option_None

