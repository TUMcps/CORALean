module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorBoxFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepErrorLeFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepErrorNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallSubsetDiagonal

@[expose] public section

/-!
# The float error box holds the exact one

`timePointStepErrorBoxFloat` denotes the box `[-ε, ε]ⁿ` for the float radius `ε`, which is at
least the exact radius `timePointStepError` (`timePointStepError_le_float`), itself non-negative,
so the exact box lies inside it. That is the direction an inner approximation needs: what is
taken off a step may only grow.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The float box denotes the box of its stored radius. -/
theorem aux_errorBoxFloat_nominal (ε : 𝕋) :
    (nominal (⟨n, fun _ => zero, diagonalBlock fun _ => ε, Interval.point fun _ => zero⟩ :
      Zonotope (Vec 𝕋 n))) =
      (⟨n, 0, Matrix.diagonal fun _ => toReal ε⟩ : Real.Zonotope (Vec ℝ n)) := by -- --- PROOF ---
  show (⟨n, toRealVec fun _ => (zero : 𝕋), fun j i => toReal (diagonalBlock (fun _ => ε) j i)⟩
    : Real.Zonotope (Vec ℝ n)) = _
  have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := by
    funext i; simp [toRealVec, toReal_zero]
  have hG : (fun (j : Fin n) (i : Fin n) => toReal (diagonalBlock (fun _ : Fin n => ε) j i))
      = Matrix.diagonal fun _ => toReal ε := by
    funext j i
    rw [toReal_diagonalBlock]
    simp only [toRealVec, Matrix.diagonal_apply]
  rw [hc, hG]

/-- A box of non-negative radius lies in the closed ball of that radius. -/
theorem aux_diagonal_subset_closedBall {ε : ℝ} (hε : 0 ≤ ε) :
    (⟨n, 0, Matrix.diagonal fun _ => ε⟩ : Real.Zonotope (Vec ℝ n)).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) ε := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hε]
  intro i
  -- the coordinate is its own coefficient times the radius
  have : (0 + ∑ j, β j • (Matrix.diagonal fun _ => ε) j) i = β i * ε := by
    rw [zero_add, Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Matrix.diagonal_apply_ne _ hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Real.norm_eq_abs]
  show |(0 + ∑ j, β j • (Matrix.diagonal fun _ => ε) j) i| ≤ ε
  rw [this, abs_mul, abs_of_nonneg hε]
  exact mul_le_of_le_one_left hε (hβ i)

/-- The closed ball of the float radius lies in the float box. -/
theorem aux_closedBall_subset_float (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) (U : Zonotope (Vec 𝕋 n)) :
    Metric.closedBall (0 : Vec ℝ n) (toReal (sys.timePointStepErrorFloat r η U))
      ⊆ ContSet.construct (sys.timePointStepErrorBoxFloat r η U) := by -- --- PROOF ---
  intro x hx
  refine ⟨x, ?_, 0, ?_, add_zero x⟩
  · -- the nominal part is the diagonal zonotope of the float radius
    show x ∈ ContSet.construct (nominal (⟨n, fun _ => zero,
      diagonalBlock fun _ => sys.timePointStepErrorFloat r η U, Interval.point fun _ => zero⟩ :
        Zonotope (Vec 𝕋 n)))
    rw [aux_errorBoxFloat_nominal]
    exact Real.Zonotope.closedBall_subset_diagonal _ hx
  · -- the error box is the stored origin
    have h : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := by
      funext i; simp [toRealVec, toReal_zero]
    rw [← h]
    exact Interval.mem_point (fun _ : Fin n => (zero : 𝕋))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.timePointStepErrorBox_subset_float (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) (U : Zonotope (Vec 𝕋 n)) :
    (sys.timePointStepErrorBox (toReal r) η (nominal U)).construct ⊆
      ContSet.construct (sys.timePointStepErrorBoxFloat r η U) := by -- --- PROOF ---
  -- the exact radius is non-negative, so its box is its ball, which the float radius covers
  have hA : toRealMat sys.A ∈ (Interval.point sys.A).construct := Interval.mem_point sys.A
  have hε' : ‖toReal r • toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2
  have h0 := sys.timePointStepError_nonneg hr η (nominal U) hε'
  exact (aux_diagonal_subset_closedBall h0).trans
    ((Metric.closedBall_subset_closedBall (sys.timePointStepError_le_float hr hη U)).trans
      (aux_closedBall_subset_float sys r η U))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
