import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.plusA`

Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. Entries are copied and the off-blocks are
`zero`, so nothing here rounds.
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

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. Entries are copied and the off-blocks are
`zero`, so nothing here rounds. -/
def ConPolyZono.plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat 𝕋 m₁ s₁) (A₂ : Mat 𝕋 m₂ s₂) :
    Mat 𝕋 (m₁ + m₂) (s₁ + s₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (A₂ r)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
