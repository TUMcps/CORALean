module

public import CORALean.ContDynamics.LinearARX.Operations.InputMat
public import CORALean.ContDynamics.LinearARX.Operations.OutputEq
public import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
public import CORALean.ContDynamics.LinearARX.Theorems.OutputEqMulVec
public import CORALean.ContDynamics.LinearARX.Theorems.SumBlock

@[expose] public section

/-!
# An input cannot reach the first block of the window early

The input enters the last block of the window, and `A_ext` shifts a block one place per step,
so it needs `p-1` steps to reach the first block: `C₀ A_ext^a B_ext_j = 0` for `a < p-1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A_ext` carries block `r+1` into block `r`, for `r+1 < p`. -/
theorem LinearARX.aux_shift (sys : LinearARX 𝕋 dy du p) (w : Vec ℝ (p * dy)) (r : ℕ)
    (hr : r + 1 < p) (b : Fin dy) :
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
theorem LinearARX.aux_pow_shift (sys : LinearARX 𝕋 dy du p) (w : Vec ℝ (p * dy)) (a : ℕ) :
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.outputC_pow_mulVec_inputMat (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) {a : ℕ}
    (ha : a + 1 < p) (j : Fin (p + 1)) (v : Vec ℝ du) :
    toRealMat sys.outputEq.C *ᵥ (toRealMat sys.toLinearSysDT.A ^ a
      *ᵥ (toRealMat (sys.inputMat j) *ᵥ v)) = 0 := by -- --- PROOF ---
  funext r
  rw [LinearARX.outputEq_C_mulVec sys hp, LinearARX.aux_pow_shift sys _ a 0 (by omega) r]
  simp only [Matrix.mulVec, dotProduct, toRealMat_apply, LinearARX.inputMat, Matrix.of_apply,
    Equiv.symm_apply_apply, zero_add, if_neg (show ¬ a + 1 = p by omega),
    ExactScalar.toReal_zero, zero_mul, Finset.sum_const_zero, Pi.zero_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
