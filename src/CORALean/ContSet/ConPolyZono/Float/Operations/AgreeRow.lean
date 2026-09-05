import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.agreeRow`

The row pinning the two points together in one coordinate. Entries are
copied and `neg` is exact, so nothing here rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The row pinning the two points together in coordinate `i`. Entries are
copied and `neg` is exact, so nothing here rounds. -/
def ConPolyZono.agreeRow (C₁ C₂ : ConPolyZono 𝕋 n) (i : Fin n) :
    Fin (C₁.h + C₂.h) → 𝕋 :=
  Fin.append (fun l => C₁.G i l) fun l => neg (C₂.G i l)

end CORALean.Float
