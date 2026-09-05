import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.plusB`

The two right-hand sides side by side, each bound concatenated with its own.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

/-- The two right-hand sides side by side, each bound concatenated with its
own. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval (Vec ℝ m₁)) (b₂ : Interval (Vec ℝ m₂)) :
    Interval (Vec ℝ (m₁ + m₂)) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩

end CORALean.Real
