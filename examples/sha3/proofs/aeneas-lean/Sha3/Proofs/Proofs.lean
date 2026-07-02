import Sha3.Extraction.Specs
import Sha3.Proofs.MissingSpecs
import Hax

namespace sha3

open Std.Do Aeneas implementation
open Aeneas.Std hiding namespace core alloc
open CoreModels
set_option mvcgen.warning false

abbrev inst := U64.Insts.Sha3ImplementationKeccakItem1

attribute [local spec] uncurry

/-
We prove two examples of equivalences between implementaiton and reference:

## Part 1: Equivalence of `iota`

Both implementations of iota yield the same state array, provided that the argument `i` is small
enough. (Otherwise both implementations would access the round constants array out of bounds.)
-/

@[spec]
theorem implementation.iota.spec.proof
  (st : implementation.KeccakState Std.U64 1#usize) (i : Std.Usize) :
  (implementation.iota.pre st i).holds →
  ⦃ ⌜ True ⌝ ⦄
  implementation.iota st i
  ⦃ ⇓ res => ⌜ (implementation.iota.post st i res).holds ⌝ ⦄ := by
  -- Unfold all definitions
  unfold implementation.iota KeccakState.iota KeccakState.Insts.CoreOpsIndexIndexPairUsizeUsizeT.index get_ij
    iota.pre core.slice.Slice.len at *
  dsimp only [U64.Insts.Sha3ImplementationKeccakItem1.xor_constant, _veorq_n_u64, KeccakState.set, set_ij, iota.post,
    reference.iota]
  -- Call `hax_mvcgen`. This tactic will run `mvcgen` on triples in both hypotheses and in goals
  hax_mvcgen
  -- This yields 9 verification conditions, which `grind` can largely discharge:
  · grind
  · grind
  · grind
  · grind
  · grind
  · expose_names
    unfold ROUNDCONSTANTS reference.ROUND_CONSTANTS at *;
    have : r_10 = r_9 ^^^ r_8 := by grind
    simp_all only [UScalar.ofNatCore_val_eq]
    grind
  · grind
  · grind
  · grind

/-
## Part 2: Equivalence of `round`

To demonstrate how we can incrementally prove equivalence of functions, we skip verification
of `theta`, `rho`, `pi`, and `chi` and show how we can prove equivalence of the `round`
function without unfolding the underlying greek-letter functions.
-/

/- ### Skip proof of `theta`, `rho`, `pi`, and `chi`: -/

@[spec]
theorem implementation.theta.spec.proof
  (st : KeccakState Std.U64 1#usize) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakState.theta inst st
    ⦃ ⇓ r => ⌜ (post st r.swap).holds ⌝ ⦄ := by
  sorry

@[spec]
theorem implementation.pi.spec.proof
  (st : KeccakState Std.U64 1#usize) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakState.pi inst st
    ⦃ ⇓ r => ⌜ (post st r).holds ⌝ ⦄ := by
  sorry

@[spec]
theorem implementation.chi.spec.proof
  (st : KeccakState Std.U64 1#usize) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakState.chi inst st
    ⦃ ⇓ r => ⌜ (post st r).holds ⌝ ⦄ := by
  sorry

theorem rho_spec
  (st : KeccakState Std.U64 1#usize) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakState.rho inst st t
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

/- ### Panic-freedom of the reference implementations

We will also ignore the concrete implementations of the reference functions `theta`, `rho`, `pi`,
`chi`, and `iota`, but we need to know that they do not panic:
-/

theorem reference_theta_spec (st) :
    ⦃ ⌜ True ⌝ ⦄
    reference.theta st
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

theorem reference_rho_spec (st) :
    ⦃ ⌜ True ⌝ ⦄
    reference.rho st
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

theorem reference_pi_spec (st) :
    ⦃ ⌜ True ⌝ ⦄
    reference.pi st
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

theorem reference_chi_spec (st) :
    ⦃ ⌜ True ⌝ ⦄
    reference.chi st
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

theorem reference_iota_spec (st i) :
    ⦃ ⌜ True ⌝ ⦄
    reference.iota st i
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

/- ### Encapsulation specifications

When running `mvcgen` on a program, we need specifications for all contained functions. For the
reference functions and for the implementation `rho`, we do not have a specification. We want
to abstract over whatever these functions are doing. For that purpose, we can use
`core.Result.toPure_spec` to encapsulate their implementations and keep them opaque to mvcgen.
It produces specifications such as:
```
⦃⌜True⌝⦄ rho st t ⦃ ⇓r => ⌜r = (rho st t).toPure⌝ ⦄
```
In essence, this states that `rho` does whatever `rho` does, and it prevents `mvcgen` from getting
stuck at `rho` while putting some useful information into the verification conditions.

-/

-- Some `Inhabited` instances are currently required for `core.Result.toPure_spec`
instance : Inhabited (KeccakState Std.U64 1#usize) := ⟨{st := ⟨List.replicate 25 0#u64, by simp⟩}⟩
instance [Inhabited α] : Inhabited (Std.Array α n) := ⟨⟨List.replicate n.val default, by simp⟩⟩

@[spec]
def rho_spec' {st} {t} := Std.Result.toPure_spec (KeccakState.rho inst st t) (rho_spec st)

@[spec]
def reference_theta_spec' {st} := Std.Result.toPure_spec (reference.theta st) (reference_theta_spec st)

@[spec]
def reference_rho_spec' {st} := Std.Result.toPure_spec (reference.rho st) (reference_rho_spec st)

@[spec]
def reference_pi_spec' {st} := Std.Result.toPure_spec (reference.pi st) (reference_pi_spec st)

@[spec]
def reference_chi_spec' {st} := Std.Result.toPure_spec (reference.chi st) (reference_chi_spec st)

@[spec]
def reference_iota_spec' {st i} := Std.Result.toPure_spec (reference.iota st i) (reference_iota_spec st i)


/- ### Equivalence proof

Now we can prove equivalence for `round`:
-/

attribute [spec]
  iota.pre chi.post iota.post pi.post round.post round.pre
  theta.post core.slice.Slice.len

@[spec]
theorem round_spec
  (st : KeccakState Std.U64 1#usize) (i : Std.Usize)
  (h : (round.pre st i).holds) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakState.round inst st i
    ⦃ ⇓ r => ⌜ (round.post st i r).holds ⌝ ⦄ := by
  unfold KeccakState.round at *
  hax_mvcgen [implementation.KeccakState.Insts.CoreCloneClone.clone, core.Array.Insts.CoreCloneClone.clone] -- Try `hax_mvcgen -trivial` to see some exemplary verification conditions here

end sha3
