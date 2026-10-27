module

public import CORALean.ContSet.Zonotope.Float.Theorems.VecExact
public import CORALean.ContSet.Zonotope.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# `Zonotope.vec` decides whether a matrix zonotope is a single matrix

CORA's `representsa(matZ, 'point')` is the test on the stacked zonotope. A `true` from the float
test says the stacked set is one vector, and stacking is a bijection, so the matrix zonotope is
one matrix.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* `h` – the float test on the stacked zonotope is `true`

## Conclusion
* the matrix zonotope denotes a single matrix
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

theorem Zonotope.vec_representsa_point_sound {Z : Zonotope (Mat 𝕋 m n)}
    (h : Z.vec.representsa_point = true) :
    ∃ A, Z.construct = {A} := by
  obtain ⟨v, hv⟩ := Zonotope.representsa_point_sound h
  refine ⟨matVecEquiv.symm v, ?_⟩
  rw [Zonotope.vec_exact, ← matVecEquiv.apply_symm_apply v, ← Set.image_singleton] at hv
  exact matVecEquiv.injective.image_injective hv

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
