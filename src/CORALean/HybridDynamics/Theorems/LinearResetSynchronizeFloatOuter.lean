module

public import CORALean.HybridDynamics.Operations.LinearResetSynchronizeFloat
public import CORALean.HybridDynamics.Operations.LinearResetSynchronize
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# The float `synchronize` encloses the real matrix

The real `A` that `LinearReset.synchronize` returns for the real values of the stored matrices
lies, entry by entry, between the bounds `synchronizeFloat` returns. An outer statement; the
bounds are not the sum.

## Inputs
* `W` – float reset matrices
* `w` – float reset offsets
* `idStates` – states kept by identity
* `i` – row
* `l` – column

## Hypotheses
* none

## Conclusion
* the real matrix entry lies between the float bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.synchronizeFloat_outer (W : Fin k → Mat 𝕋 n n) (w : Fin k → Vec 𝕋 n)
    (idStates : Finset (Fin n)) (i l : Fin n) : -- --- CONCL ---
    toReal ((synchronizeFloat W w idStates).1.1 i l) ≤
        (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).1 i l ∧
      (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).1 i l ≤
        toReal ((synchronizeFloat W w idStates).1.2 i l) := by -- --- PROOF ---
  -- the added identity entry is `1` on the chosen diagonal and `0` elsewhere, exactly
  have hd : toReal (if i = l ∧ i ∈ idStates then (one : 𝕋) else zero) =
      (Matrix.diagonal (fun i => if i ∈ idStates then (1 : ℝ) else 0)) i l := by
    by_cases h : i = l ∧ i ∈ idStates
    · obtain ⟨rfl, hi⟩ := h
      simp [hi, toReal_one]
    · rw [if_neg h, toReal_zero, Matrix.diagonal_apply]
      by_cases hil : i = l
      · subst hil
        simp [(not_and.mp h) rfl]
      · simp [hil]
  -- the real `A` is the entrywise sum of the matrices plus that diagonal
  have hA : (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).1 i l =
      ∑ j, toReal (W j i l) +
        (Matrix.diagonal (fun i => if i ∈ idStates then (1 : ℝ) else 0)) i l := by
    simp only [synchronize, Matrix.add_apply]
    congr 1
    erw [Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [hA]
  -- each direction pays its own roundings, the sum's and the addition's
  refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
  · rw [hd]
    exact add_le_add_left (sumDown_le_sum _) _
  · rw [hd]
    exact add_le_add_left (sum_le_sumUp _) _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
