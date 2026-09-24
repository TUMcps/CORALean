import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Operations.PowRange
import CORALean.NN.Layers.Theorems.LeMulRangeUp
import CORALean.NN.Layers.Theorems.MulRangeDownLe

/-!
# A power is inside its bracket

By induction on the exponent, each step one product bracket.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem powRange_bounds (t : 𝕋) (k : ℕ) :
    toReal (powRange t k).1 ≤ toReal t ^ k
      ∧ toReal t ^ k ≤ toReal (powRange t k).2 := by -- --- PROOF ---
  induction k with
  | zero =>
    -- `one` is exact, so the empty product is bracketed by itself
    rw [pow_zero]
    exact ⟨le_of_eq toReal_one, le_of_eq toReal_one.symm⟩
  | succ k ih =>
    have hcomm : toReal t ^ (k + 1) = toReal t * toReal t ^ k := by ring
    refine ⟨?_, ?_⟩
    · show toReal (mulRangeDown t (powRange t k).1 (powRange t k).2) ≤ _
      rw [hcomm]
      exact mulRangeDown_le ih.1 ih.2
    · show _ ≤ toReal (mulRangeUp t (powRange t k).1 (powRange t k).2)
      rw [hcomm]
      exact le_mulRangeUp ih.1 ih.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
