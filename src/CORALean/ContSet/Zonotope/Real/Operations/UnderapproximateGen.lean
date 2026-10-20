module

public import CORALean.ContSet.Zonotope.Real.Operations.Underapproximate

@[expose] public section

/-!
# `Zonotope.underapproximateGen`

`underapproximate` at CORA's default direction set `S = G`, which CORA takes when the generator
matrix has at least as many rows as columns (`n ≥ h`); the other default, `dominantDirections`, is
`Zonotope.dominantDirections`, whose answer `underapproximate` takes as its `S`.

## Inputs
* `n` – dimension
* `Z` – zonotope

## Output
* extremal point per generator and sign
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's default direction set `S = G`, for a zonotope with `h ≤ n`. -/
noncomputable def Zonotope.underapproximateGen {n : ℕ} (Z : Zonotope (Vec ℝ n)) :
    Fin Z.h → Bool → Vec ℝ n :=
  Z.underapproximate Z.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
