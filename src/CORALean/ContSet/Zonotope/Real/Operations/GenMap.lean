import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# `Zonotope.genMap`

The generators read as a linear map from coefficients to the ambient space, so
that `construct` is the centre plus this map's image of the unit box.

Named because a constraint on points becomes a constraint on coefficients by
composing with it, which is how a halfspace description turns into a constrained
zonotope.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.genMap (Z : Zonotope α) : Vec ℝ Z.h →ₗ[ℝ] α where
  toFun β := ∑ j, β j • Z.G j
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' a u := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul]
    exact (Finset.smul_sum).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
