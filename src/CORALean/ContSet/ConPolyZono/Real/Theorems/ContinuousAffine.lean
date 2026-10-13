import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
import CORALean.ContSet.ConPolyZono.Real.Operations.Affine
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The map a constrained polynomial zonotope is the image of is continuous

Independent coefficients enter linearly and dependent factors through a
monomial, so `continuous_monomial` is the only step a zonotope's version does
not have. It is what carries compactness from the coefficient domain onto the
set.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.continuous_affine (cPZ : ConPolyZono α) :
    Continuous cPZ.affine := by -- --- PROOF ---
  unfold ConPolyZono.affine
  refine (continuous_const.add (continuous_finsetSum _ fun i _ => ?_)).add
    (continuous_finsetSum _ fun j _ => ?_)
  · exact ((PolyZonotope.continuous_monomial cPZ.E i).comp continuous_fst).smul continuous_const
  · exact ((continuous_apply j).comp continuous_snd).smul continuous_const

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
