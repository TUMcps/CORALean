import CORALean.HybridDynamics.Operations.LinearResetSynchronizeFloat
import CORALean.HybridDynamics.Operations.LinearResetSynchronize
import Mathlib.Algebra.BigOperators.Pi

/-!
# The float `synchronize` encloses the real offset

The real `c` that `LinearReset.synchronize` returns for the real values of the stored offsets
lies, entry by entry, between the bounds `synchronizeFloat` returns. An outer statement.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.synchronizeFloat_offset_outer (W : Fin k → Mat 𝕋 n n)
    (w : Fin k → Vec 𝕋 n) (idStates : Finset (Fin n)) (i : Fin n) :
    toReal ((synchronizeFloat W w idStates).2.1 i) ≤
        (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).2 i ∧
      (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).2 i ≤
        toReal ((synchronizeFloat W w idStates).2.2 i) := by -- --- PROOF ---
  -- the real `c` is the entrywise sum of the offsets
  have hc : (synchronize (toRealMat ∘ W) (toRealVec ∘ w) idStates).2 i = ∑ j, toReal (w j i) := by
    simp only [synchronize]
    erw [Finset.sum_apply]
    rfl
  rw [hc]
  exact ⟨sumDown_le_sum _, sum_le_sumUp _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
