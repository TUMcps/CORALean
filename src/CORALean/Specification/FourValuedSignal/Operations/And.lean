module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.And
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Operations.Or
public import CORALean.Specification.KleeneSignal.Operations.Until
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The conjunction of four-valued signals

`sig = fourValuedSignal.and_(varargin)`: the Kleene conjunction of the refinements with
inconclusive mapped to `False` is the Kleene part, and the value is inconclusive where it differs
from that with inconclusive mapped to `True`; `none` is the `toBoolSignal()` error, which `at_and`
shows does not occur. This is `Λ̃₁ ∧ Λ̃₂` of [1, Sec. 4.3 (operators)], the `⊔₂` of the
conjunctions of `⌊Λ̃⌋` and `⌈Λ̃⌉`.
Refinement pending: CORA computes this in doubles, its refinement over `𝕋` is not yet written.

## Inputs
* `ι` – index type of the operands
* `sigs` – four-valued signals to conjoin

## Output
* the conjunction signal, or none if CORA throws

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = fourValuedSignal.and_(varargin)`; `none` if `toBoolSignal()` throws. -/
noncomputable def FourValuedSignal.and_ {ι : Type} [Fintype ι] (sigs : ι → FourValuedSignal ℝ) :
    Option (FourValuedSignal ℝ) :=
  -- 1. minAnd of the refinements with inconclusive mapped to False
  let minRefinements := fun k => (sigs k).toKleeneSignal Kleene.ff
  let minAnd := KleeneSignal.and_ minRefinements
  -- 2. maxAnd of the refinements with inconclusive mapped to True
  let maxRefinements := fun k => (sigs k).toKleeneSignal Kleene.tt
  let maxAnd := KleeneSignal.and_ maxRefinements
  -- 3. inc = kleeneSignal.combine(@(args) kleene.fromBool(range(args) ~= 0),min,max).toBoolSignal()
  let inc := (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
    Kleene.fromBool (decide (args 0 ≠ args 1))) ![minAnd, maxAnd] ()).toBoolSignal?
  inc.map fun inc => ⟨minAnd, inc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
