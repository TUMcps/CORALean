import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.andB`

The right-hand side of `andDep`: the two systems' own bounds, then the
agreement rows' `c₂ − c₁` widened by the tolerance.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The right-hand side of `andDep`: the two systems' own bounds, then the
agreement rows' `c₂ − c₁` widened by the tolerance. -/
def ConPolyZono.andB (C₁ C₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    Interval (Vec ℝ (C₁.m + C₂.m + n)) :=
  ⟨Fin.append (ConPolyZono.plusB C₁.b C₂.b).inf fun i => C₂.c i - C₁.c i + D.inf i,
   Fin.append (ConPolyZono.plusB C₁.b C₂.b).sup fun i => C₂.c i - C₁.c i + D.sup i⟩

end CORALean.Real
