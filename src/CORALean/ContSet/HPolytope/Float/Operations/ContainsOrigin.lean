module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.containsOrigin`

Whether the origin is certified to meet every row of the nominal part: each inequality's bound
with its slack, rounded down, is at least `0`, and each equality's right-hand side lies within
its slack of `0` (`HPolytope.containsOrigin_sound`). The error box is not read: the test is of
the nominal part, which is what a constrained zonotope's coefficient polytope denotes. `false`
says only that the origin was not certified.

## Inputs
* `P` – H-polytope

## Output
* every slack-widened inequality bound certified nonnegative, every equality within its slack
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

/-- Every inequality's slack-widened bound certified nonnegative, every equality's right-hand side
certified within its slack. -/
def HPolytope.containsOrigin (P : HPolytope 𝕋 (Vec 𝕋 n)) : Bool :=
  (List.finRange P.m).all (fun i => le zero (addDown (P.b i) (absolute (P.b_error i))))
    && (List.finRange P.me).all (fun i => le (absolute (P.be i)) (absolute (P.be_error i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
