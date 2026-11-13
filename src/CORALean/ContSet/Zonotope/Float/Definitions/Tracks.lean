module

public import CORALean.ContSet.Zonotope.Float.Definitions.ContainsAt

@[expose] public section

/-!
# A zonotope that keeps the generators of another in front

`Y` tracks `f` over `X` when `Y` has at least the generators of `X`, and a point `x` of `X` at the
weights `β` is mapped to a point `f x` of `Y` at weights that begin with `β`: the first generators
of `Y` are the images of those of `X`, and the others, which the map adds, are fresh. It is what
lets a set built from `X` and from its image share the dependence of the one on the other.

## Inputs
* `X` – zonotope
* `Y` – image of the zonotope
* `f` – map

## Output
* proposition that the image tracks the map over the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.Tracks (X : Zonotope (Vec 𝕋 n)) (Y : Zonotope (Vec 𝕋 m))
    (f : Vec ℝ n → Vec ℝ m) : Prop :=
  ∃ hle : X.h ≤ Y.h, ∀ (β : Vec ℝ X.h) (x : Vec ℝ n), X.ContainsAt β x →
    ∃ γ : Vec ℝ Y.h, (∀ j : Fin X.h, γ (Fin.castLE hle j) = β j) ∧ Y.ContainsAt γ (f x)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
