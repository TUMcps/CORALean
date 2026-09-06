import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes

/-!
# `mtimes` does not change the ball's dimension
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Ellipsoid.mtimes_k (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (Ellipsoid.mtimes M E).k = E.k := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
