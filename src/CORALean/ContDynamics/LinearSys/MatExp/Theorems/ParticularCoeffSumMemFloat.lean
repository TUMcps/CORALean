module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSum
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSumFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# `Σᵢ Ãᵢ` lies in its float box

`Σᵢ Ãᵢ` of eq. (25) in [1, Prop. 11], by induction on `η`: each `Ãᵢ` at a member `M` is in
`intervalInputTerm` (`smul_pow_mem_intervalInputTerm`), `matPlus` holds the sum of members,
and an empty range sums to `0`, which the point `0` holds.

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

/-- At every member `M` of `A` and `Δt ≥ 0`, the exact `Σᵢ₌ᵢ₀^η Ãᵢ` is in the float sum. -/
theorem MatExp.particularCoeffSum_mem (A : Interval (Mat 𝕋 n n)) {r : 𝕋} (hr : 0 ≤ toReal r)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) (i0 η : ℕ) :
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
