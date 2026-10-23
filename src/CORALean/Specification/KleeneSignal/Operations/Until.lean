module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The until of three-valued signals

`sig = until(lhs,interval,rhs)` of `kleeneSignal.m`: the until of the minimal refinements (unknown
as false) is the Boolean part, and the value is unknown where it differs from that of the maximal
refinements (unknown as true). This is `Λ₁ U_I Λ₂` of [1, Sec. 4.2 (operators)]: the `⊔₁` of the
untils of `⌊Λ⌋` and `⌈Λ⌉`.
Refinement pending: CORA computes this in doubles, its refinement over `𝕋` is not yet written.

## Inputs
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal

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

/-- `sig = until(lhs,interval,rhs)`. -/
noncomputable def KleeneSignal.until (lhs : KleeneSignal ℝ) (interval : STLInterval ℝ)
    (rhs : KleeneSignal ℝ) : KleeneSignal ℝ :=
  -- 1. minUntil of the refinements with unknown mapped to false
  let lhsMinRefinement := lhs.toBoolSignal false
  let rhsMinRefinement := rhs.toBoolSignal false
  let minUntil := lhsMinRefinement.until interval rhsMinRefinement
  -- 2. maxUntil of the refinements with unknown mapped to true
  let lhsMaxRefinement := lhs.toBoolSignal true
  let rhsMaxRefinement := rhs.toBoolSignal true
  let maxUntil := lhsMaxRefinement.until interval rhsMaxRefinement
  -- 3. unk = pointSegmentSignal.combine(@(args) args(1) ~= args(2),minUntil,maxUntil)
  let unk := PointSegmentSignal.combine
    (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1)) ![minUntil, maxUntil] ()
  ⟨minUntil, unk⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
