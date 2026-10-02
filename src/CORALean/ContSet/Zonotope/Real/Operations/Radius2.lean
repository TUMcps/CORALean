import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Radius2

/-!
# `Zonotope.radius₂`

CORA's `@zonotope/radius`: the smaller of two radii of a ball about the centre. One is the sum of
the generator lengths `∑ⱼ ‖Gⱼ‖₂`, the other the Euclidean norm of the half-widths of `interval(Z)`
(`Interval.radius₂`, CORA's `norm(rad(IH))`). Both are upper bounds on the distance of a member to
the centre, so the minimum is one too, but not the smallest such radius: that needs
`max_β ‖∑ βⱼ Gⱼ‖₂`, which CORA does not compute.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/radius`. -/
noncomputable def Zonotope.radius₂ (Z : Zonotope (Vec ℝ n)) : ℝ :=
  min (∑ j, ‖Z.G j‖₂) Z.interval.radius₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
