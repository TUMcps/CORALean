module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Zonotope.generatorLength`

CORA's `@zonotope/generatorLength.m`: `vecnorm(Z.G)`, the Euclidean length of each generator.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
