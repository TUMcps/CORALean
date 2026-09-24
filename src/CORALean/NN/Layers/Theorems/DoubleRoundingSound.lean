import CORALean.NN.Layers.Operations.DoubleRounding

/-!
# Self-addition rounds doubling

Each direction of the self-sum is on its side of `x + x = 2x`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem doubleRounding_sound : (doubleRounding (𝕋 := 𝕋)).Sound 2 where
  up_ge x := by have h := add_le_addUp x x; show _ ≤ toReal (addUp x x); linarith
  down_le x := by have h := addDown_le_add x x; show toReal (addDown x x) ≤ _; linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
