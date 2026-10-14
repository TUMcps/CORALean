module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Interval.radius₂`

CORA's `@interval/radius`: the Euclidean norm of the half-widths, `sqrt(sum(rad(I).^2))`. Not
`Interval.radius`, which is CORA's `rad`, the half-width vector itself. `Theorems/Radius2IsLeast`
says what it measures: the radius of the smallest Euclidean ball about the centre containing the
box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval/radius`. -/
noncomputable def Interval.radius₂ (I : Interval (Vec ℝ n)) : ℝ := ‖I.radius‖₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
