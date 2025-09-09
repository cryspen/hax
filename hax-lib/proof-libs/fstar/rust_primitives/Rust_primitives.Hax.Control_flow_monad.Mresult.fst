module Rust_primitives.Hax.Control_flow_monad.Mresult

let run #a #e (f: Core_models.Result.t_Result (Core_models.Result.t_Result a e) e): Core_models.Result.t_Result a e
    = match f with
    | Core_models.Result.Result_Ok x -> x 
    | Core_models.Result.Result_Err e -> Core_models.Result.Result_Err e

