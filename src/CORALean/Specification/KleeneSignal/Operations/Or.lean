module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The disjunction of three-valued signals

`sig = kleeneSignal.or_(varargin)`: the Boolean combination `@any` of the minimal refinements
(unknown as false) is the Boolean part, and the value is unknown where it differs from that of the
maximal refinements (unknown as true).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = kleeneSignal.or_(varargin)`. -/
noncomputable def KleeneSignal.or_ {ι : Type} [Fintype ι] (sigs : ι → KleeneSignal ℝ) :
    KleeneSignal ℝ :=
  -- 1. minRefinements with unknown mapped to false, and their `@any`
  let minRefinements := fun k => (sigs k).toBoolSignal false
  let minOr := PointSegmentSignal.combine
    (fun (args : ι → Bool) (_ : Unit) => decide (∃ k, args k = true)) minRefinements ()
  -- 2. maxRefinements with unknown mapped to true, and their `@any`
  let maxRefinements := fun k => (sigs k).toBoolSignal true
  let maxOr := PointSegmentSignal.combine
    (fun (args : ι → Bool) (_ : Unit) => decide (∃ k, args k = true)) maxRefinements ()
  -- 3. unk = pointSegmentSignal.combine(@(args) range(args) ~= 0,min,max)
  let unk := PointSegmentSignal.combine
    (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1))
    ![minOr, maxOr] ()
  ⟨minOr, unk⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
