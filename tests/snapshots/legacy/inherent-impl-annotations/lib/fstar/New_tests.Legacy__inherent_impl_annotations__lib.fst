module New_tests.Legacy__inherent_impl_annotations__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

type t_OnMethod = | OnMethod : t_OnMethod

#push-options "--z3rlimit 111"

let impl_OnMethod__annotated_method (_: Prims.unit) : u8 = mk_u8 0

#pop-options

let before_method = "before method"

let impl_OnMethod__quoted_method (_: Prims.unit) : u8 = mk_u8 1

let after_method = "after method"

type t_OnBlock = | OnBlock : t_OnBlock

let before_block = "before block"

let impl_OnBlock__first (_: Prims.unit) : u8 = mk_u8 0

let impl_OnBlock__second (_: Prims.unit) : u8 = mk_u8 1

let after_block = "after block"

type t_OnBlockOptions = | OnBlockOptions : t_OnBlockOptions

#push-options "--z3rlimit 222"

let impl_OnBlockOptions__first (_: Prims.unit) : u8 = mk_u8 0

let impl_OnBlockOptions__second (_: Prims.unit) : u8 = mk_u8 1

#pop-options

type t_OnBlockWithConst = | OnBlockWithConst : t_OnBlockWithConst

#push-options "--z3rlimit 333"

let impl_OnBlockWithConst__C: u8 = mk_u8 3

let impl_OnBlockWithConst__f (_: Prims.unit) : u8 = impl_OnBlockWithConst__C

#pop-options
