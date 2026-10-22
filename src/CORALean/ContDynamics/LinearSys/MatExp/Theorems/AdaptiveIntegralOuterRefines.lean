module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdaptiveRemainderSubsetIntervalInputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSum
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSumFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# The float `eAtInt` holds the exact one

A member `X` of the exact `Asum + Δt [-W, W]` is `Asum` plus a member of `Δt [-W, W]`: the
first is in the float `particularCoeffSum` (`aux_particularCoeffSum_mem`), the second in the float
`intervalInputRemainder` (`adaptiveRemainder_subset_intervalInputRemainder`), and `matPlus`
holds their sum.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hr` – step length nonnegative
* `hε` – float norm bound small enough for the Taylor order
* `hM` – member lies in the interval matrix

## Conclusion
* the exact integrated exponential lies in the float one

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- At every member `M` of `A` and `Δt ≥ 0`, the exact `Σᵢ₌ᵢ₀^η Ãᵢ` is in the float sum. -/
theorem MatExp.aux_particularCoeffSum_mem (A : Interval (Mat 𝕋 n n)) {r : 𝕋} (hr : 0 ≤ toReal r)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) (i0 η : ℕ) : -- --- CONCL ---
    Real.MatExp.particularCoeffSum M (toReal r) i0 η
      ∈ (MatExp.particularCoeffSum A r i0 η).construct := by -- --- PROOF ---
  -- the point `0` holds the empty sum
  have hzero : (0 : Mat ℝ n n)
      ∈ (Interval.point fun _ _ => (zero : 𝕋) : Interval (Mat 𝕋 n n)).construct :=
    Interval.mem_mat_iff.mpr fun _ _ => by simp [Interval.point, toReal_zero]
  have hterm : ∀ i, Real.MatExp.particularCoeff M (toReal r) i
      ∈ (MatExp.intervalInputTerm A r i).construct :=
    fun i => MatExp.smul_pow_mem_intervalInputTerm A hr hM i
  induction η with
  | zero =>
    unfold Real.MatExp.particularCoeffSum MatExp.particularCoeffSum
    split_ifs with h
    · subst h; simpa using hterm 0
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]; exact hzero
  | succ η ih =>
    unfold Real.MatExp.particularCoeffSum MatExp.particularCoeffSum
    split_ifs with h
    · rw [Finset.sum_Ico_succ_top h, Interval.materialiseMat_eq]
      exact Interval.matPlus_outer _ _ ih (hterm (η + 1))
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]; exact hzero


-- =======================================  MAIN THEOREM  ======================================= --

/-- At every member `M` of `A`, `Δt ≥ 0` and an order the float remainder admits, the exact
`eAtInt` of `errorSolution_adaptive`, remainder [1, Lemma 1]'s, lies in the float one. -/
theorem MatExp.adaptiveIntegral_outer_refines (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) : -- --- CONCL ---
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
    have h := MatExp.aux_particularCoeffSum_mem A hr hM 0 η
    rwa [Real.MatExp.particularCoeffSum, ← Finset.range_eq_Ico] at h
  rw [show X = S + (X - S) by abel]
  unfold MatExp.adaptiveIntegral
  rw [Interval.materialiseMat_eq]
  exact Interval.matPlus_outer _ _ hsum
    (MatExp.adaptiveRemainder_subset_intervalInputRemainder A hr η hε hM hrem)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
