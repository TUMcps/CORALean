import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.plusB`

The two right-hand sides side by side. Copied, so nothing here rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two right-hand sides side by side. Copied, so nothing here rounds. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval 𝕋 m₁) (b₂ : Interval 𝕋 m₂) :
    Interval 𝕋 (m₁ + m₂) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
