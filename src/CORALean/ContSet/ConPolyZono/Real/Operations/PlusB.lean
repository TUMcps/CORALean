import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.plusB`

The two right-hand sides side by side, each bound concatenated with its own.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two right-hand sides side by side, each bound concatenated with its
own. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval (Vec ℝ m₁)) (b₂ : Interval (Vec ℝ m₂)) :
    Interval (Vec ℝ (m₁ + m₂)) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
