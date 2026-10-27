module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The conjunction of three-valued signals

`sig = kleeneSignal.and_(varargin)`: the Boolean `@all` of the minimal refinements (unknown as
false) is the Boolean part, and the value is unknown where it differs from that of the maximal
refinements (unknown as true). This is `Λ₁ ∧ Λ₂` of [1, Sec. 4.2 (operators)]: the `⊔₁` of the
conjunctions of `⌊Λ⌋` and `⌈Λ⌉`.

## Inputs
* `ι` – index type of the operands
* `sigs` – three-valued signals to conjoin

## Output
* the conjunction signal

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
    [TimeOrder 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = kleeneSignal.and_(varargin)`. -/
def KleeneSignal.and_ {ι : Type} [FinEnum ι] (sigs : ι → KleeneSignal 𝕋) : KleeneSignal 𝕋 :=
  -- 1. minRefinements with unknown mapped to false, and their `@all`
  let minRefinements := fun k => (sigs k).toBoolSignal false
  let minAnd := PointSegmentSignal.combine
    (fun (args : ι → Bool) (_ : Unit) => decide (∀ k, args k = true)) minRefinements ()
  -- 2. maxRefinements with unknown mapped to true, and their `@all`
  let maxRefinements := fun k => (sigs k).toBoolSignal true
  let maxAnd := PointSegmentSignal.combine
    (fun (args : ι → Bool) (_ : Unit) => decide (∀ k, args k = true)) maxRefinements ()
  -- 3. unk = pointSegmentSignal.combine(@(args) range(args) ~= 0,min,max)
  let unk := PointSegmentSignal.combine
    (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1))
    ![minAnd, maxAnd] ()
  ⟨minAnd, unk⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
