module

public import CORALean.ContSet.Zonotope.Float.Theorems.VecExact
public import CORALean.ContSet.Zonotope.Float.Theorems.RepresentsaOriginSound

@[expose] public section

/-!
# `Zonotope.vec` decides whether a matrix zonotope is the zero matrix

CORA's `representsa(matZ, 'origin')` is the test on the stacked zonotope. A `true` from the float
test says the stacked set is the origin, and stacking is a bijection, so the matrix zonotope is
the zero matrix.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* `h` – the float test on the stacked zonotope is `true`

## Conclusion
* the matrix zonotope denotes exactly the zero matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vec_representsa_origin_sound {Z : Zonotope (Mat 𝕋 m n)}
    (h : Z.vec.representsa_origin = true) :
    Z.construct = {0} := by
  have h1 := Zonotope.representsa_origin_sound h
  rw [Zonotope.vec_exact, ← map_zero matVecEquiv, ← Set.image_singleton] at h1
  exact matVecEquiv.injective.image_injective h1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
