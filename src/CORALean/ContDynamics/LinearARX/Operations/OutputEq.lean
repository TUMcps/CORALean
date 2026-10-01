import CORALean.ContDynamics.LinearARX.LinearARX
import CORALean.ContDynamics.OutputEq.OutputEq

/-!
# The output equation of the converted system

`y(k)` is block `0` of the window `stack y k`: `C` picks it, and `D = 0`, the input
being already in the state's next window.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [Zero 𝕋] [One 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.outputEq (_sys : LinearARX 𝕋 dy du p) : OutputEq 𝕋 (p * dy) (p * dy) dy where
  C := Matrix.of fun r c =>
    if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then 1 else 0
  D := 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
