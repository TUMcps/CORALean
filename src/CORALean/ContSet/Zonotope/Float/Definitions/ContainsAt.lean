module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A point of a float zonotope at given weights of its generators

`Z.toSet` says that a point is in the zonotope for some weights of the generators; `ContainsAt`
names the weights. A point is in `Z` at `β` when, in every coordinate, it is the stored center
plus the generators weighted by `β` plus a point of the error box. What an operation does to the
weights, rather than to the set, is stated with it: the same `β` for the generators it keeps.

## Inputs
* `Z` – zonotope
* `β` – weights of the generators
* `x` – point

## Output
* proposition that the point is in the zonotope at the weights
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.ContainsAt (Z : Zonotope (Vec 𝕋 n)) (β : Vec ℝ Z.h) (x : Vec ℝ n) : Prop :=
  (∀ j, |β j| ≤ 1) ∧ ∃ e ∈ Z.I_error.toSet,
    ∀ i, x i = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * β j + e i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
