module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.representsaFullspace` over a floating-point scalar

`polytope/representsa_` at type `'fullspace'`, H-representation, tolerance `0`: every
inequality row is `0 ≤ b` with `b ≥ 0`, every equality row is `0 x = be` with `be = 0`, and the
error box is not empty (otherwise the polytope would be). Each comparison is a `le`, certified
when it answers `true` only, so the test is sound when `true` and says nothing when `false`.

## Inputs
* `P` – H-polytope

## Output
* `true` when every row is `0 ≤ b` with `b ≥ 0` or `0 = 0` and the error box is nonempty
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.representsaFullspace (P : HPolytope 𝕋 (Vec 𝕋 n)) : Bool :=
  (List.finRange P.m).all (fun i =>
    le zero (P.b i) && (List.finRange n).all fun j => le (P.A i j) zero && le zero (P.A i j)) &&
  (List.finRange P.me).all (fun r =>
    (le (P.be r) zero && le zero (P.be r)) &&
    (List.finRange n).all fun j => le (P.Ae r j) zero && le zero (P.Ae r j)) &&
  (List.finRange n).all fun j => le (P.I_error.inf j) (P.I_error.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
