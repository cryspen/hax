module Core.Slice.Iter

open Core
open Core.Types

let t_Chunks a = slice (slice a)
let t_ChunksExact a = slice (slice a)
let t_Iter a = slice a



// instance chunks_it a: iterator (t_Chunks a) = 

