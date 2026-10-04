import CORALean.HybridDynamics.Operations.NonlinearResetSynchronizeFloat
import CORALean.HybridDynamics.Theorems.NonlinearResetEvaluateSynchronize
import Mathlib.Algebra.BigOperators.Pi

/-!
# The synchronized float model encloses the synchronized reset

If every `fms j` encloses `rs j`, then `synchronize fms idStates` encloses `synchronize rs
idStates`: the pre-jump value at `idStates` plus the sum of the component values, in directed
rounding. An outer statement.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.FloatModel.Encloses.synchronize
    {fms : Fin k → NonlinearReset.FloatModel 𝕋 n m n} {rs : Fin k → NonlinearReset n m n}
    (h : ∀ j, (fms j).Encloses (rs j)) (idStates : Finset (Fin n)) :
    (NonlinearReset.FloatModel.synchronize fms idStates).Encloses
      (NonlinearReset.synchronize rs idStates) := by -- --- PROOF ---
  refine ⟨fun X U x hx u hu i => ?_⟩
  -- each component value is in its box
  have hj := fun j => (h j).f_mem X U x hx u hu
  -- the added pre-jump value, or zero, is in its (exact) box
  have hd : toReal (if i ∈ idStates then X.inf i else zero) ≤ (if i ∈ idStates then x i else 0) ∧
      (if i ∈ idStates then x i else 0) ≤ toReal (if i ∈ idStates then X.sup i else zero) := by
    by_cases hi : i ∈ idStates
    · simpa [hi] using (show toReal (X.inf i) ≤ x i ∧ x i ≤ toReal (X.sup i) from hx i)
    · simp [hi, toReal_zero]
  show toReal (addDown _ _) ≤ (NonlinearReset.synchronize rs idStates).evaluate x u i ∧ _
  rw [NonlinearReset.evaluate_synchronize]
  exact ⟨le_trans (addDown_le_add _ _) (add_le_add hd.1 (le_trans (sumDown_le_sum _)
      (Finset.sum_le_sum fun j _ => (hj j i).1))),
    le_trans (add_le_add hd.2 (le_trans (Finset.sum_le_sum fun j _ => (hj j i).2)
      (sum_le_sumUp _))) (add_le_addUp _ _)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
