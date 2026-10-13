import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.plusG`

The two scaled generator blocks side by side, each rounded down.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two scaled generator blocks side by side, each rounded down. -/
def Ellipsoid.plusG (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append (fun j => mulDown s₁ (E₁.G i j)) (fun j => mulDown s₂ (E₂.G i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
