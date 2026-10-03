import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.EuclideanNorm

/-!
# `Zonotope.generatorLength`

CORA's `@zonotope/generatorLength.m`: `vecnorm(Z.G)`, the Euclidean length of each generator.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Euclidean length `‖Gⱼ‖₂` of generator `j`. -/
noncomputable def Zonotope.generatorLength (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  ‖Z.G j‖₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
