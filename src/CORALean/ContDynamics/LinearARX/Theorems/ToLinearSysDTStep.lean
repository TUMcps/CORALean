import CORALean.ContDynamics.LinearARX.Operations.Feed
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
import CORALean.ContDynamics.LinearARX.Theorems.SumBlock
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The converted system takes the ARX step

On windows of an ARX run, `A x(k) + feed u k` is `x(k+1)`. Block `a < p-1` is a
shift, and the last block is the recursion at `k + p`, with `Fin.rev` turning the
column `a'` back into the lag `i = p-1-a'` it carries. Stated at `ℝ`, where
`toRealMat` is the identity and the block matrices can be read off entrywise.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product with a block vector, at one coordinate, as a double sum. -/
theorem LinearARX.aux_mulVec_block {m : ℕ} (M : Mat ℝ (p * dy) m) (x : Vec ℝ m) (a : Fin p)
    (b : Fin dy) :
    (M *ᵥ x) (finProdFinEquiv (a, b)) = ∑ c, M (finProdFinEquiv (a, b)) c * x c := rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.toLinearSysDT_step (sys : LinearARX 𝕋 dy du p) {y : ℕ → Vec ℝ dy}
    {u : ℕ → Vec ℝ du}
    (hy : ∀ k, p ≤ k →
      y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
        + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)) (k : ℕ) :
    LinearARX.stack p y (k + 1)
      = toRealMat sys.toLinearSysDT.A *ᵥ LinearARX.stack p y k + sys.feed u k := by -- --- PROOF ---
  funext r
  -- read one coordinate, block `a`, component `b`
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective r
  have hfeed : sys.feed u k (finProdFinEquiv (a, b)) =
      if a.val + 1 = p then
        ∑ j : Fin (p + 1), (toRealMat (sys.Bbar j) *ᵥ u (k + p - j)) b else 0 := by
    -- the input signal lives in the last block only
    unfold LinearARX.feed
    rw [Finset.sum_apply]
    split_ifs with h
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [LinearARX.inputMat, Matrix.mulVec, dotProduct, Scalar.toRealMat_apply,
        Matrix.of_apply, Equiv.symm_apply_apply, if_pos h]
    · refine Finset.sum_eq_zero fun j _ => ?_
      simp only [LinearARX.inputMat, Matrix.mulVec, dotProduct, Scalar.toRealMat_apply,
        Matrix.of_apply, Equiv.symm_apply_apply, if_neg h, ExactScalar.toReal_zero, zero_mul,
        Finset.sum_const_zero]
  rw [Pi.add_apply, hfeed, LinearARX.aux_mulVec_block, LinearARX.sum_block]
  simp only [LinearARX.stack, LinearARX.toLinearSysDT, Matrix.of_apply, Equiv.symm_apply_apply,
    Scalar.toRealMat_apply]
  -- a shift row, or the last row carrying the recursion
  by_cases h1 : a.val + 1 < p
  · have h2 : ¬ a.val + 1 = p := by omega
    simp only [if_pos h1, if_neg h2, add_zero]
    rw [Finset.sum_eq_single (⟨a.val + 1, h1⟩ : Fin p)]
    · rw [Finset.sum_eq_single b]
      · simp only [and_self, if_true, ExactScalar.toReal_one, one_mul]
        congr 1; omega
      · intro b' _ hb'
        simp [hb', ExactScalar.toReal_zero]
      · simp
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun b' _ => ?_
      have : ¬ (a'.val = a.val + 1) := fun h => ha' (Fin.ext h)
      simp [this, ExactScalar.toReal_zero]
    · simp
  · have h2 : a.val + 1 = p := by omega
    simp only [if_neg h1, if_pos h2]
    have e : k + 1 + a.val = k + p := by omega
    -- the recursion at `k + p`, its lags reindexed by `Fin.rev`
    rw [e, hy (k + p) (by omega), Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    congr 1
    rw [← Equiv.sum_comp Fin.revPerm
      (fun i => ∑ x_1, Scalar.toReal (sys.Abar i.rev b x_1) * y (k + ↑i) x_1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : k + (Fin.rev i).val = k + p - (i.val + 1) := by rw [Fin.val_rev]; omega
    rw [this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
