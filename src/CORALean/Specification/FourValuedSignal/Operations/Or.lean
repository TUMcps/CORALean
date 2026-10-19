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
# The disjunction of four-valued signals

`sig = fourValuedSignal.or_(varargin)`: the Kleene disjunction of the refinements with inconclusive
mapped to `False` is the Kleene part, and the value is inconclusive where it differs from the
disjunction of the refinements with inconclusive mapped to `True`. `toBoolSignal()` throws if a
value is unknown; `none` is that error, which `at_or` shows does not occur.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = fourValuedSignal.or_(varargin)`; `none` if `toBoolSignal()` throws. -/
noncomputable def FourValuedSignal.or_ {ι : Type} [Fintype ι] (sigs : ι → FourValuedSignal ℝ) :
    Option (FourValuedSignal ℝ) :=
  -- 1. minOr of the refinements with inconclusive mapped to False
  let minRefinements := fun k => (sigs k).toKleeneSignal Kleene.ff
  let minOr := KleeneSignal.or_ minRefinements
  -- 2. maxOr of the refinements with inconclusive mapped to True
  let maxRefinements := fun k => (sigs k).toKleeneSignal Kleene.tt
  let maxOr := KleeneSignal.or_ maxRefinements
  -- 3. inc = kleeneSignal.combine(@(args) kleene.fromBool(range(args) ~= 0),min,max).toBoolSignal()
  let inc := (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
    Kleene.fromBool (decide (args 0 ≠ args 1))) ![minOr, maxOr] ()).toBoolSignal?
  inc.map fun inc => ⟨minOr, inc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
