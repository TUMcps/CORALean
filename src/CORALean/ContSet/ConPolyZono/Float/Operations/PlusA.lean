module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.plusA`

Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. Entries are copied and the off-blocks are
`zero`, so nothing here rounds.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. Entries are copied and the off-blocks are
`zero`, so nothing here rounds. -/
def ConPolyZono.plusA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁) (A₂ : Mat 𝕋 m₂ q₂) :
    Mat 𝕋 (m₁ + m₂) (q₁ + q₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (A₂ r)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
