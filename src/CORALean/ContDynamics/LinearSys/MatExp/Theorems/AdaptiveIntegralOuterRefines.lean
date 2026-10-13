import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdaptiveRemainderSubsetIntervalInputRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularCoeffSumMemFloat

/-!
# The float `eAtInt` holds the exact one

A member `X` of the exact `Asum + Δt [-W, W]` is `Asum` plus a member of `Δt [-W, W]`: the
first is in the float `particularCoeffSum` (`particularCoeffSum_mem`), the second in the float
`intervalInputRemainder` (`adaptiveRemainder_subset_intervalInputRemainder`), and `matPlus`
holds their sum.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At every member `M` of `A`, `Δt ≥ 0` and an order the float remainder admits, the exact
`eAtInt` of `errorSolution_adaptive`, remainder [1, Lemma 1]'s, lies in the float one. -/
theorem MatExp.adaptiveIntegral_outer_refines (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    (Real.MatExp.adaptiveIntegral M (toReal r) η).construct
      ⊆ (MatExp.adaptiveIntegral A r η).construct := by -- --- PROOF ---
  intro X hX
  set S := ∑ i ∈ Finset.range (η + 1), Real.MatExp.particularCoeff M (toReal r) i with hS
  -- `X - Asum` is in the exact remainder box, so in the float one
  have hrem : X - S ∈ (Real.MatExp.adaptiveRemainder M (toReal r) η).construct := by
    have hX' := Real.Interval.mem_mat_iff.mp hX
    refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
    simp only [Real.MatExp.adaptiveIntegral, Real.MatExp.adaptiveRemainder] at hX' ⊢
    rw [Matrix.sub_apply]
    constructor <;> linarith [(hX' j k).1, (hX' j k).2]
  -- `Asum` is the float sum's from order `0`
  have hsum : S ∈ (MatExp.particularCoeffSum A r 0 η).construct := by
    have h := MatExp.particularCoeffSum_mem A hr hM 0 η
    rwa [Real.MatExp.particularCoeffSum, ← Finset.range_eq_Ico] at h
  rw [show X = S + (X - S) by abel]
  unfold MatExp.adaptiveIntegral
  rw [Interval.materialiseMat_eq]
  exact Interval.matPlus_outer _ _ hsum
    (MatExp.adaptiveRemainder_subset_intervalInputRemainder A hr η hε hM hrem)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
