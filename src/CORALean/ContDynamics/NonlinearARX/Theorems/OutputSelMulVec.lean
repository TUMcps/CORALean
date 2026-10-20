module

public import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The selection matrix reads the output off the window

`y(k)` is block `0` of the window `stack p y k`, which `outputSel` selects; at `p = 0` the
window is empty and says nothing about `y`.

## Inputs
* `sys` – ARX system
* `y` – outputs
* `k` – step

## Hypotheses
* `hp` – at least one lag

## Conclusion
* the selection matrix applied to the window gives the output
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {dy du p : ℕ}
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.outputSel_mulVec (sys : NonlinearARX dy du p) (hp : 0 < p)
    (y : ℕ → Vec ℝ dy) (k : ℕ) : -- --- CONCL ---
    toRealMat (sys.outputSel (𝕋 := 𝕋)) *ᵥ NonlinearARX.stack p y k = y k := by -- --- PROOF ---
  -- the selection matrix reads as the real 0/1 selection
  have hsel : toRealMat (sys.outputSel (𝕋 := 𝕋)) =
      Matrix.of fun (r : Fin dy) (c : Fin (p * dy)) =>
        if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then (1 : ℝ)
        else 0 := by
    funext r c
    rw [Scalar.toRealMat_apply]
    simp only [NonlinearARX.outputSel, Matrix.of_apply]
    split_ifs
    · exact CORALean.Float.SoundFloatArithmetic.toReal_one
    · exact CORALean.Float.SoundFloatArithmetic.toReal_zero
  rw [hsel]
  -- one row: only the entry `(0, r)` of the window survives the sum
  funext r
  simp only [Matrix.mulVec, dotProduct]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · rw [Finset.sum_eq_single r]
    · simp only [Matrix.of_apply, Equiv.symm_apply_apply, and_self,
        if_true, one_mul, NonlinearARX.stack, Nat.add_zero]
    · intro b _ hb
      simp only [Matrix.of_apply, Equiv.symm_apply_apply, true_and,
        if_neg hb, zero_mul]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ¬ a.val = 0 := fun h => ha (Fin.ext h)
    simp only [Matrix.of_apply, Equiv.symm_apply_apply, this,
      false_and, if_false, zero_mul]
  · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
