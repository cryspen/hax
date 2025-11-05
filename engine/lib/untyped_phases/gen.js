#!/usr/bin/env node
const { readdirSync, readFileSync } = require('fs');

let f = s => ((s.split("include module type")[0] || "").match(/(with|and) type[^)]*/g) || []).join("").split('and type').map(x => x.replace(/(with|and) type/g, '').trim()).filter(x => x).map(x => x.split('=')[1].trim().split('.').slice(1));

let phases = readdirSync("../phases").filter(x => x.endsWith(".mli")).map(filename => ({
  filename,
  contents: f(readFileSync("../phases/" + filename).toString()),
}));

let rejections = readFileSync("../phases/phase_reject.ml")
  .toString()
  .split('\n')
  .map(s => s.match(/^module ([a-z][a-z_]+)/i)?.[1])
  .filter(s => s);

console.log(`
open Prelude
    
module type PHASE_FULL =
  Phase_utils.PHASE
    with module FA = Features.Full
     and module FB = Features.Full
     and module A = Ast.Full
     and module B = Ast.Full

module BindPhaseFull (A : PHASE_FULL) (B : PHASE_FULL) : PHASE_FULL = struct
  include Phase_utils.BindPhase (A) (B)
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full
end

module IdentityFull : PHASE_FULL = struct
  include Phase_utils.Identity (Features.Full)
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full
end

let bind (module A : PHASE_FULL) (module B : PHASE_FULL) : (module PHASE_FULL) =
  (module BindPhaseFull (A) (B))

let bind_list : (module PHASE_FULL) list -> (module PHASE_FULL) =
  List.reduce ~f:bind
  >> Option.value ~default:(module IdentityFull : PHASE_FULL)

`);


for (let phase of phases) {
  let name_lc = phase.filename.replace(/^phase_/, "").replace(/[.]mli$/, "");
  let name = name_lc.replace(/^(.)/, l => l.toUpperCase());
  phase.name_lc = name_lc;
  phase.name = name;
  phase.module_expression = `Phases.${name}`;
}


for (let rejection of rejections) {
  let name = 'Reject_' + rejection.replace(/^(.)/, l => l.toLowerCase()).replace(/[A-Z]/g, c => `_${c}`).toLowerCase();
  phases.push({
    name_lc: name.toLowerCase(),
    name,
    module_expression: 'Phase_reject.' + rejection,
    contents: [],
  });
}

phases.push({
  name_lc: "hoist_side_effects",
  name: 'Hoist_side_effects',
  module_expression: 'Side_effect_utils.Hoist',
  contents: [
    ['Off', 'monadic_binding'],
    ['Off', 'for_index_loop'],
  ],
});


for (let phase of phases) {
  let { name, module_expression } = phase;

  console.log(`
module ${name} : PHASE_FULL = struct
  module FA = Features.Full
  module FB = Features.Full
  module A = Ast.Full
  module B = Ast.Full

  module ExpectedFA = struct
    open Features
    include On
    ${phase.contents.map(([status, f]) => `include ${status}.${f.replace(/^(.)/, l => l.toUpperCase())}`).join('\n')}
  end

  module Phase = ${module_expression} (ExpectedFA)

  module Coerce =
    Feature_gate.Make (Features.Full) (ExpectedFA)
      (struct
        module A = Features.Full
        module B = ExpectedFA
        include Feature_gate.DefaultSubtype

        ${phase.contents.map(([status, f]) =>
    `let ${f} = ` + (status == 'On' ? 'fun _ _ -> Features.On.' + f : 'reject')
  ).join('\n')}

        let metadata =
          Phase_reject.make_metadata
            (CoercionForUntypedPhase
               ([%show: Diagnostics.Phase.t] Phase.metadata.current_phase))
      end)

  let metadata = Phase.metadata
  let to_full_ast : Phase.B.item list -> Ast.Full.item list = Stdlib.Obj.magic

  let ditems =
    List.map ~f:Coerce.ditem >> List.concat >> Phase.ditems >> to_full_ast
end
`);
}


for (let phase of phases) {
  console.log(`let ${phase.name_lc} : (module PHASE_FULL) = (module ${phase.name})`)
}
console.log(`let phases_list : (module PHASE_FULL) list = [${phases.map(p => p.name_lc).join(';')}]`)


console.log(`
let phase_of_name: string -> (module PHASE_FULL) option = 
    function
    ${phases.map(p => `| "${p.name_lc}" -> Some ${p.name_lc}`).join('')}
    | _ -> None

let phases: string list = [${phases.map(p => `"${p.name_lc}"`).join(';')}]

(*
${phases.map(p => `${p.name_lc}`).join(', ')}
*)
`);




