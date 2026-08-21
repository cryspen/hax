module Core_models.Ops.Try_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_FromResidual as t_FromResidual}

include Core_models.Bundle {f_from_residual_pre as f_from_residual_pre}

include Core_models.Bundle {f_from_residual_post as f_from_residual_post}

include Core_models.Bundle {f_from_residual as f_from_residual}

include Core_models.Bundle {t_Try as t_Try}

include Core_models.Bundle {f_Output as f_Output}

include Core_models.Bundle {f_Residual as f_Residual}

include Core_models.Bundle {f_from_output_pre as f_from_output_pre}

include Core_models.Bundle {f_from_output_post as f_from_output_post}

include Core_models.Bundle {f_from_output as f_from_output}

include Core_models.Bundle {f_branch_pre as f_branch_pre}

include Core_models.Bundle {f_branch_post as f_branch_post}

include Core_models.Bundle {f_branch as f_branch}

include Core_models.Bundle {t_Residual as t_Residual}

include Core_models.Bundle {f_TryType as f_TryType}

include Core_models.Bundle {t_Yeet as t_Yeet}

include Core_models.Bundle {Yeet as Yeet}
