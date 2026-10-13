import CORALean.ContSet.ConZonotope.Real.ConZonotope
import Mathlib.Data.Finset.Sort

/-!
# `ConZonotope.compactEmbed`

The coefficients of the kept generators `S`, put back into the full coefficient space with
zero in every dropped coordinate, the kept ones in order. Composing a constraint with it reads
the constraint at a point whose dropped coefficients are zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `v` at the kept coordinates of `S`, zero elsewhere: `∑ l, v l • e_{S l}`. -/
def ConZonotope.compactEmbed {h : ℕ} (S : Finset (Fin h)) : Vec ℝ S.card →ₗ[ℝ] Vec ℝ h where
  toFun v := ∑ l, v l • (Pi.single (S.orderIsoOfFin rfl l).1 (1 : ℝ) : Vec ℝ h)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
