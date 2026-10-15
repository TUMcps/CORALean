module

public import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
public import CORALean.ContDynamics.LinearARX.Theorems.OutputPowInputMat
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTIsTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.IsTrajectoryStateEq

@[expose] public section

/-!
# `computeGO` gives the output of every ARX run

`y(k) = C{k} y₀ + ∑_i D{k,i} u(i)`, with `y₀` the initial window, for every run of the model:
the window runs through `toLinearSysDT`, its closed form is `state_eq`, and the first block is
the output. The inputs that `D` leaves out are exactly those `A_ext` has not carried to the
first block yet, which is `outputC_pow_mulVec_inputMat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Mtimes Matrix

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.computeGO_output (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) {Y₀ : S (p * dy)}
    {U : S du} {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.IsTrajectory Y₀ U y u)
    {nk : ℕ} (k : Fin nk) :
    y k.val = (sys.computeGO nk).C k *ᵥ LinearARX.stack p y 0
      + ∑ i : Fin nk, (sys.computeGO nk).D k i *ᵥ u i := by -- --- PROOF ---
  -- the output is the first block of the window, whose closed form is `state_eq`
  have hy : y k.val = toRealMat sys.outputEq.C *ᵥ LinearARX.stack p y k.val := by
    funext r
    rw [LinearARX.outputEq_C_mulVec sys hp]
    simp [LinearARX.stack]
  rw [hy, (sys.toLinearSysDT_isTrajectory traj).state_eq k.val]
  simp only [LinearARX.computeGO, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_sum,
    LinearARX.feed, Matrix.sum_mulVec]
  congr 1
  -- both sides run over the steps `t < k` and the lags `j`; the right one over `i` as well
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht := Finset.mem_range.mp ht
  have hk := k.isLt
  by_cases h : t + p - j.val < nk
  · rw [Finset.sum_eq_single (⟨t + p - j.val, h⟩ : Fin nk)]
    · simp
      rw [Matrix.mul_assoc]
    · intro i _ hi
      have : ¬ t + p - j.val = i.val := fun e => hi (Fin.ext e.symm)
      simp [this]
    · simp
  · -- an input read after step `k` cannot reach the output yet
    rw [Finset.sum_eq_zero fun i _ => by
      have : ¬ t + p - j.val = i.val := by have := i.isLt; omega
      simp [this]]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine LinearARX.outputC_pow_mulVec_inputMat sys hp ?_ j _
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
