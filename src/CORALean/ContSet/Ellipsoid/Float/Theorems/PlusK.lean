import CORALean.ContSet.Ellipsoid.Float.Operations.Plus

/-!
# `plus`'s ball dimension is the sum of the two incoming ones
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Ellipsoid.plus_k (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).k = E₁.k + E₂.k := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
