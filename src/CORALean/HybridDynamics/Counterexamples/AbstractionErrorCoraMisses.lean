module

public import CORALean.HybridDynamics.Counterexamples.AbstractionErrorCoraEqZero
public import CORALean.HybridDynamics.Operations.SdcFlow
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.HybridDynamics.Definitions.SdcInput
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's printed `aux_abstractionError` misses the abstraction error

CORA's `aux_abstractionError` with `err1` overwritten in its loop (`GuardMap.abstractionErrorCora`)
against the difference `x(t) − y(t)` of a run and the constant flow that
`GuardMap.abstractionError` holds (`GuardMap.abstractionError_outer`). In `ℝ³` take the shift
`A = [0 1 0; 0 0 1; 0 0 0]`, no inputs, `R₀ = {(0, 0, 1)}`, `tmax = 2`, `th = 1`, `η = 3`: at
`t = 2` the error is `(1, 0, 0)`, the dropped summand `t(A²/2)(t − th)x₀` of `err1`. CORA keeps
`(A³/6)(…) = 0` and, `W` being zero, its set is `{0}` (`GuardMap.abstractionErrorCora_eq_zero`).
No `A` with `A² ≠ 0` has `W = 0` in two dimensions.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's error set misses the true abstraction error
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The shift of `ℝ³`. -/
private def aux_absErrCoraCex_A : Mat ℝ 3 3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

private theorem aux_absErrCoraCex_sq : aux_absErrCoraCex_A ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_three, aux_absErrCoraCex_A]

private theorem aux_absErrCoraCex_cube : aux_absErrCoraCex_A ^ 3 = 0 := by
  rw [pow_succ, aux_absErrCoraCex_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, aux_absErrCoraCex_A]

/-- A matrix with `M³ = 0` has `e^M` its Taylor polynomial of order `3`. -/
private theorem aux_absErrCoraCex_exp {M : Mat ℝ 3 3} (hM : M ^ 3 = 0) :
    exp M = MatExp.expTaylor M 3 := by
  rw [exp_eq_tsum ℝ, MatExp.expTaylor]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : 3 ≤ k := by simp at hk; omega
  rw [show k = 3 + (k - 3) by omega, pow_add, hM, zero_mul, smul_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `GuardMap.abstractionErrorCora` misses the error `x(t) − y(t)` of a run from `x₀ ∈ R₀` with
inputs in `U`, `t ∈ [0, tmax]`, `th = tmax/2`, `η = 3`, which `GuardMap.abstractionError` holds. -/
theorem GuardMap.abstractionErrorCora_counterexample : -- --- CONCL ---
    ∃ (A : Mat ℝ 3 3) (U R₀ : Zonotope (Vec ℝ 3)) (tmax t : ℝ) (x₀ : Vec ℝ 3)
      (u : ℝ → Vec ℝ 3), t ∈ Set.Icc 0 tmax ∧ x₀ ∈ R₀.construct ∧
      (∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ U.construct) ∧
      AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t)) ∧
      exp (t • A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
          - GuardMap.sdcFlow A (GuardMap.sdcInput A U.c (tmax / 2) 3 R₀.c) x₀ t
        ∉ (GuardMap.abstractionErrorCora A U R₀ (tmax / 2) tmax
          3).construct := by -- --- PROOF ---
  refine ⟨aux_absErrCoraCex_A, Zonotope.ofPoint 0, Zonotope.ofPoint ![0, 0, 1], 2, 2,
    ![0, 0, 1], fun _ => 0,
    ⟨by norm_num, le_rfl⟩, Zonotope.mem_ofPoint _, fun _ _ => Zonotope.mem_ofPoint _,
    aestronglyMeasurable_const, ?_⟩
  -- `|A| = A`, so `W = e^{2A} − T₃(2A) = 0`, and CORA's set is `{0}`
  have h3 : ∀ s : ℝ, (s • aux_absErrCoraCex_A) ^ 3 = 0 := fun s => by
    rw [smul_pow, aux_absErrCoraCex_cube, smul_zero]
  have habs : MatExp.absMat aux_absErrCoraCex_A = aux_absErrCoraCex_A := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [MatExp.absMat, aux_absErrCoraCex_A]
  have hW : MatExp.expRemainderMat aux_absErrCoraCex_A 2 3 = 0 := by
    rw [MatExp.expRemainderMat, habs, aux_absErrCoraCex_exp (h3 2), sub_self]
  obtain ⟨hc, hG⟩ := GuardMap.abstractionErrorCora_eq_zero aux_absErrCoraCex_A ![0, 0, 1] (2 / 2) 2
    aux_absErrCoraCex_cube hW
  rintro ⟨β, -, hβ⟩
  simp only [hc, hG, smul_zero, Finset.sum_const_zero, add_zero] at hβ
  -- the error at `t = 2` is `(1, 0, 0)`
  have h0 := congrFun hβ 0
  rw [aux_absErrCoraCex_exp (h3 2)] at h0
  simp only [MatExp.expTaylor, GuardMap.sdcFlow, GuardMap.sdcInput, Finset.sum_range_succ,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_zero, smul_pow, aux_absErrCoraCex_sq,
    aux_absErrCoraCex_cube, Zonotope.ofPoint, mulVec_zero, intervalIntegral.integral_zero,
    smul_zero, add_zero, zero_add, Nat.reduceAdd] at h0
  simp [mulVec, dotProduct, Fin.sum_univ_three, aux_absErrCoraCex_A, Nat.factorial,
    Matrix.vecHead, Matrix.vecTail] at h0
  norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
