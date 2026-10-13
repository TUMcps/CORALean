import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Supremum
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `Zonotope.constrSat`

CORA's `@zonotope/constrSat`: do all points of the zonotope satisfy `C x < d`? CORA boxes the
image, `I = interval(C*Z) + (-d)`, and answers `all(supremum(I) < 0)`: every upper bound of the
box lies below `d`. Sufficient, not necessary, as the box over-approximates the image.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/constrSat`. -/
def Zonotope.constrSat (Z : Zonotope (Vec ℝ n)) (C : Mat ℝ m n) (d : Vec ℝ m) : Prop :=
  let I := (Zonotope.mtimes C Z).interval
  ∀ i, I.supremum i - d i < 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
