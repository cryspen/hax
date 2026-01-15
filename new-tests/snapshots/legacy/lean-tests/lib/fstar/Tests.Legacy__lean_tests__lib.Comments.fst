module Tests.Legacy__lean_tests__lib.Comments
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Single line doc comment
let f (_: Prims.unit) : Prims.unit = ()

(** Block doc-comment : Lorem ipsum dolor sit amet, consectetur adipiscing elit. Vestibulum rutrum
orci ac tellus ullamcorper sollicitudin. Sed fringilla mi id arcu suscipit rhoncus. Pellentesque et
metus a ante feugiat lobortis. Nam a mauris eget nisl congue egestas. Duis et gravida
nulla. Curabitur mattis leo vel molestie posuere. Etiam malesuada et augue eget
varius. Pellentesque quis tincidunt erat. Vestibulum id consectetur turpis. Cras elementum magna id
urna volutpat fermentum. In vel erat quis nunc rhoncus porta. Aliquam sed pellentesque
tellus. Quisque odio diam, mollis ut venenatis non, scelerisque at nulla. Nunc urna ante, tristique
quis nisi quis, congue maximus nisl. Curabitur non efficitur odio. *)
let heavily_documented (_: Prims.unit) : u32 = mk_u32 4
