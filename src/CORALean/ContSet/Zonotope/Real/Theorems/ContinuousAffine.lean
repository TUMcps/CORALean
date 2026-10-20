module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# The map a zonotope is the image of is continuous

Coefficients enter linearly, so `β ↦ c + ∑ βⱼ • Gⱼ` is continuous. It is what
carries compactness from the coefficient cube onto the set, both here and for
the constrained zonotope, whose `construct` is the image of its own domain under
this same map.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the coefficient map is continuous
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.continuous_affine (Z : Zonotope α) :
    Continuous fun β : Fin Z.h → ℝ => Z.c + ∑ j, β j • Z.G j :=
  continuous_const.add (continuous_finsetSum _ fun j _ =>
    (continuous_apply j).smul continuous_const)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
