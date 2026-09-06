import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.plusGap`

How far each stored generator can be from its exact scaling.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far each stored generator can be from its exact scaling. -/
def Ellipsoid.plusGap (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append
    (fun j => subUp (mulUp s₁ (E₁.G i j)) (mulDown s₁ (E₁.G i j)))
    (fun j => subUp (mulUp s₂ (E₂.G i j)) (mulDown s₂ (E₂.G i j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
