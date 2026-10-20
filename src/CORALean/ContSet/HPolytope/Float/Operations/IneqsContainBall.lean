module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.ineqsContainBall`

Whether every inequality row keeps a whole ball around `β₀` in the supremum norm: a point within
`δ` of `β₀` in every coordinate reads row `i` at most `Aᵢ β₀ + δ ∑ⱼ |Aᵢⱼ|`, so the check is that
this, rounded up, is at most the bound with its slack, rounded down
(`HPolytope.ineqsContainBall_sound`). The equality rows are not read: they leave no room for a
ball, and a caller that needs one checks there are none.

## Inputs
* `P` – H-polytope
* `β₀` – vector of length `n`
* `δ` – scalar

## Output
* `true` when every inequality row, moved by `δ` from `β₀`, is certified within its bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every inequality row, moved by `δ` in every coordinate from `β₀`, certified within its bound
and slack. -/
def HPolytope.ineqsContainBall (P : HPolytope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 n) (δ : 𝕋) : Bool :=
  (List.finRange P.m).all fun i =>
    le (addUp (dotUp (P.A i) β₀) (mulUp δ (radius P.A i)))
      (addDown (P.b i) (absolute (P.b_error i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
