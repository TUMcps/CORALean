import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.intersectionB`

The right-hand side of `intersectionDep`: the two systems' own bounds, then the
agreement rows' `c₂ − c₁` widened by the tolerance.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand side of `intersectionDep`: the two systems' own bounds, then the
agreement rows' `c₂ − c₁` widened by the tolerance. -/
def ConPolyZono.intersectionB (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    Interval (Vec ℝ (cPZ₁.m + cPZ₂.m + n)) :=
  ⟨Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).inf fun i => cPZ₂.c i - cPZ₁.c i + D.inf i,
   Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).sup fun i => cPZ₂.c i - cPZ₁.c i + D.sup i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
