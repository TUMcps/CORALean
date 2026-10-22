module

public import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
public import CORALean.ContDynamics.LinearARX.Operations.InputMat
public import CORALean.ContDynamics.LinearARX.Operations.OutputEq
public import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
public import CORALean.ContDynamics.LinearARX.Operations.Simulate
public import CORALean.ContDynamics.LinearARX.Theorems.Basic
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTIsTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.IsTrajectoryStateEq

@[expose] public section

/-!
# `computeGO` gives the output of every ARX run

`y(k) = C{k} y₀ + ∑_i D{k,i} u(i)`, with `y₀` the initial window, for every run of the model:
the window runs through `toLinearSysDT`, its closed form is `state_eq`, and the first block is
the output. The inputs that `D` leaves out are exactly those `A_ext` has not carried to the
first block yet, which is `aux_outputC_pow_mulVec_inputMat`.

## Inputs
* `sys` – ARX system
* `Y₀` – initial window set
* `U` – input set
* `y` – outputs
* `u` – inputs
* `nk` – number of steps
* `k` – step index

## Hypotheses
* `hp` – at least one lag
* `traj` – ARX trajectory

## Conclusion
* the output is the initial-window term plus the weighted inputs
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The output equation reads the first block. -/
theorem LinearARX.aux_outputEq_C_mulVec (sys : LinearARX 𝕋 dy du p) (hp : 0 < p)
    (w : Vec ℝ (p * dy)) (r : Fin dy) : -- --- CONCL ---
    (toRealMat sys.outputEq.C *ᵥ w) r = w (finProdFinEquiv (⟨0, hp⟩, r)) := by -- --- PROOF ---
  simp only [Matrix.mulVec, dotProduct, toRealMat_apply, LinearARX.outputEq, Matrix.of_apply]
  -- only the column `(0, r)` carries a `1`
  rw [Finset.sum_eq_single (finProdFinEquiv (⟨0, hp⟩, r))]
  · simp [ExactScalar.toReal_one]
  · intro c _ hc
    have : ¬ ((finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r) := by
      rintro ⟨h1, h2⟩
      apply hc
      rw [← Equiv.symm_apply_eq]
      exact Prod.ext (Fin.ext h1) h2
    rw [if_neg this, ExactScalar.toReal_zero, zero_mul]
  · simp


/-- `A_ext` carries block `r+1` into block `r`, for `r+1 < p`. -/
theorem LinearARX.aux_shift (sys : LinearARX 𝕋 dy du p) (w : Vec ℝ (p * dy)) (r : ℕ)
    (hr : r + 1 < p) (b : Fin dy) : -- --- CONCL ---
    (toRealMat sys.toLinearSysDT.A *ᵥ w) (finProdFinEquiv (⟨r, by omega⟩, b))
      = w (finProdFinEquiv (⟨r + 1, hr⟩, b)) := by -- --- PROOF ---
  rw [Matrix.mulVec, dotProduct, LinearARX.sum_block]
  simp only [LinearARX.toLinearSysDT, toRealMat_apply, Matrix.of_apply, Equiv.symm_apply_apply,
    if_pos hr]
  rw [Finset.sum_eq_single (⟨r + 1, hr⟩ : Fin p)]
  · rw [Finset.sum_eq_single b]
    · simp [ExactScalar.toReal_one]
    · intro b' _ hb'
      simp [hb', ExactScalar.toReal_zero]
    · simp
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun b' _ => ?_
    have : ¬ (a'.val = r + 1) := fun h => ha' (Fin.ext h)
    simp [this, ExactScalar.toReal_zero]
  · simp


/-- `A_ext^a` carries block `r+a` into block `r`, for `r + a < p`. -/
theorem LinearARX.aux_pow_shift (sys : LinearARX 𝕋 dy du p) (w : Vec ℝ (p * dy))
    (a : ℕ) : -- --- CONCL ---
    ∀ (r : ℕ) (hr : r + a < p) (b : Fin dy),
      (toRealMat sys.toLinearSysDT.A ^ a *ᵥ w) (finProdFinEquiv (⟨r, by omega⟩, b))
        = w (finProdFinEquiv (⟨r + a, hr⟩, b)) := by -- --- PROOF ---
  induction a with
  | zero => intro r hr b; simp
  | succ a ih =>
    intro r hr b
    rw [pow_succ', ← Matrix.mulVec_mulVec, LinearARX.aux_shift sys _ r (by omega) b,
      ih (r + 1) (by omega) b]
    have e : (⟨r + 1 + a, by omega⟩ : Fin p) = ⟨r + (a + 1), hr⟩ := Fin.ext (by simp; omega)
    rw [e]


/-- An input cannot reach the first block of the window early. -/
theorem LinearARX.aux_outputC_pow_mulVec_inputMat (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) {a : ℕ}
    (ha : a + 1 < p) (j : Fin (p + 1)) (v : Vec ℝ du) : -- --- CONCL ---
    toRealMat sys.outputEq.C *ᵥ (toRealMat sys.toLinearSysDT.A ^ a
      *ᵥ (toRealMat (sys.inputMat j) *ᵥ v)) = 0 := by -- --- PROOF ---
  funext r
  rw [LinearARX.aux_outputEq_C_mulVec sys hp, LinearARX.aux_pow_shift sys _ a 0 (by omega) r]
  simp only [Matrix.mulVec, dotProduct, toRealMat_apply, LinearARX.inputMat, Matrix.of_apply,
    Equiv.symm_apply_apply, zero_add, if_neg (show ¬ a + 1 = p by omega),
    ExactScalar.toReal_zero, zero_mul, Finset.sum_const_zero, Pi.zero_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.computeGO_output (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) {Y₀ : S (p * dy)}
    {U : S du} {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.IsTrajectory Y₀ U y u)
    {nk : ℕ} (k : Fin nk) : -- --- CONCL ---
    y k.val = (sys.computeGO nk).C k *ᵥ LinearARX.stack p y 0
      + ∑ i : Fin nk, (sys.computeGO nk).D k i *ᵥ u i := by -- --- PROOF ---
  -- the output is the first block of the window, whose closed form is `state_eq`
  have hy : y k.val = toRealMat sys.outputEq.C *ᵥ LinearARX.stack p y k.val := by
    funext r
    rw [LinearARX.aux_outputEq_C_mulVec sys hp]
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
    refine LinearARX.aux_outputC_pow_mulVec_inputMat sys hp ?_ j _
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
