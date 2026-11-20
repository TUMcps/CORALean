module

public import CORALean.ContDynamics.LinearSys.Operations.ExponentialRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExponentialRemainderOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExpRemainderMatLeExpRemainderSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec

@[expose] public section

/-!
# `MatExp.exponentialRemainder` holds the Taylor remainder, over a floating-point scalar

The exact layer's `exponentialRemainder_outer` at the real interval the stored one denotes: the
remainder of every member is within `e^N - Σ_{i ≤ η} Nⁱ/i!` of `0`, `N = abs(intMat)` read in ℝ.
`N` is the real image of the float `magnitudeMat`, nonnegative, so that bound is `E(1,η)` of `N`,
which `expRemainderSquaringFloat` bounds from above at the halvings found
(`expRemainderMat_le_expRemainderSquaringFloat`, admissible by `halvingsFloat_spec`); negation
is exact.

## Inputs
* `A` – float interval matrix
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* for the interval matrix returned, the Taylor remainder of every member lies in it
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exponentialRemainder_outer (A : Interval (Mat 𝕋 n n)) (η : ℕ) : -- --- CONCL ---
    ∀ E ∈ MatExp.exponentialRemainder A η, ∀ M : Mat ℝ n n, M ∈ A.toSet →
      exp M - Real.MatExp.expTaylor M η ∈ E.toSet := by -- --- PROOF ---
  intro E hE M hM
  rw [Option.mem_def] at hE
  simp only [MatExp.exponentialRemainder, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hE
  obtain ⟨s, hs, rfl⟩ := hE
  -- the halvings make the order `16` admissible, so `W` bounds `E(1,η)` of `abs(intMat)`
  have hadm := LinearSys.halvingsFloat_spec (η := 16) (by norm_num) s hs
  have hW := LinearSys.expRemainderMat_le_expRemainderSquaringFloat
    (LinearSys.canonicalFloat (Interval.magnitudeMat A)) η s hadm
  -- `abs(intMat)` read in ℝ is the exact layer's, and it is its own absolute value
  have hN : Real.Interval.absMax A.nominal = toRealMat (Interval.magnitudeMat A) := by
    funext i j
    simp only [Real.Interval.absMax, Interval.nominal, RealImage.realImage, toRealMat,
      Interval.magnitudeMat, toReal_maximum, toReal_absolute]
  have hNabs : Real.MatExp.absMat (toRealMat (Interval.magnitudeMat A)) =
      toRealMat (Interval.magnitudeMat A) := by
    rw [← hN]
    funext i j
    exact abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
  -- the exact layer's remainder box, entry by entry
  have hR := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.exponentialRemainder_outer A.nominal η (M := M) hM)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  have hle := hW j k
  have h := hR j k
  -- the bound of the exact layer is `E(1,η)` of `abs(intMat)`, which `W` bounds
  have e : (LinearSys.canonicalFloat (Interval.magnitudeMat A)).A = Interval.magnitudeMat A := rfl
  rw [e] at hle
  simp only [Real.MatExp.expRemainderMat, toReal_one, one_smul, hNabs, Matrix.sub_apply] at hle
  simp only [Real.MatExp.exponentialRemainder, Real.Interval.ofCenterRadius, hN,
    Matrix.sub_apply, zero_sub, zero_add, Matrix.neg_apply] at h
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.neg_apply, toReal_neg',
    Matrix.sub_apply]
  constructor <;> linarith [h.1, h.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
