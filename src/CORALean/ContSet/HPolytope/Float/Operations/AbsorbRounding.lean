module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.absorbRounding`: the errors folded into the rows

A box is not a halfspace, but its effect on one is a number: the points of `N ⊕ E` satisfy
`A x ≤ b + max_{e ∈ E} A e`. This writes every inequality row that way, its slack added:
`b + b_error + |A| r` (`bU`), rounded up. An equality has no direction to widen in, so each
becomes the two inequalities its slab and the box give, `Aₑ x ≤ bₑ + sup + |Aₑ| r` (`beU`) and
`-Aₑ x ≤ -(bₑ + inf) + |Aₑ| r` (`beLN`): the equality rows move into the inequality part. The
result has no box and no slack, so it is an ordinary description of a superset.

## Inputs
* `P` – H-polytope

## Output
* the inequalities `A x ≤ b + b_error + |A| r` and the equalities as inequality pairs, rounded up
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.absorbRounding (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := P.m + (P.me + P.me)
  A := Fin.append P.A (Fin.append P.Ae (-P.Ae))
  b := Fin.append P.bU (Fin.append P.beU P.beLN)
  me := 0
  Ae := fun i => i.elim0
  be := fun i => i.elim0
  b_error := fun _ => zero
  be_error := fun _ => zero
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
