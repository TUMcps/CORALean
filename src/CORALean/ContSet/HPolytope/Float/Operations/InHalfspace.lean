module

public import CORALean.ContSet.HPolytope.Float.Operations.EqVec
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.inHalfspace`: a polytope certified to lie in a halfspace

A row of the polytope that is the normal `a` (every entry certified equal) with a right-hand side
`bU` (slack and error box folded in, rounded up) certified at most `γ` bounds `a·x` by `γ` on the
whole polytope. `false` says nothing: a row that is a multiple of `a` is not recognised.

## Inputs
* `P` – polytope
* `a` – normal
* `γ` – offset

## Output
* whether some row certifies `P ⊆ {x | a·x ≤ γ}`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some inequality row of `P` is `a` with a bound at most `γ`. -/
def HPolytope.inHalfspace (P : HPolytope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (γ : 𝕋) : Bool :=
  (List.finRange P.m).any fun i => HPolytope.eqVec (P.A i) a && le (P.bU i) γ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
