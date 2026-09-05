import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial

/-!
# The map a constrained polynomial zonotope is the image of is continuous

Independent coefficients enter linearly and dependent factors through a
monomial, so `continuous_monomial` is the only step a zonotope's version does
not have. It is what carries compactness from the coefficient domain onto the
set.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem ConPolyZono.continuous_affine (C : ConPolyZono α) : Continuous C.affine := by
  unfold ConPolyZono.affine
  refine (continuous_const.add (continuous_finsetSum _ fun i _ => ?_)).add
    (continuous_finsetSum _ fun j _ => ?_)
  · exact ((PolyZonotope.continuous_monomial C.E i).comp continuous_fst).smul continuous_const
  · exact ((continuous_apply j).comp continuous_snd).smul continuous_const

end CORALean.Real
