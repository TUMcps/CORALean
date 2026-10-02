import CORALean.ContSet.Zonotope.Real.Operations.Underapproximate

/-!
# `Zonotope.underapproximateGen`

`underapproximate` at CORA's default direction set `S = G`, which CORA takes when the generator
matrix has at least as many rows as columns (`n ≥ h`); the other default, `dominantDirections`, is
not here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's default direction set `S = G`, for a zonotope with `h ≤ n`. -/
noncomputable def Zonotope.underapproximateGen {n : ℕ} (Z : Zonotope (Vec ℝ n)) :
    Fin Z.h → Bool → Vec ℝ n :=
  Z.underapproximate Z.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
