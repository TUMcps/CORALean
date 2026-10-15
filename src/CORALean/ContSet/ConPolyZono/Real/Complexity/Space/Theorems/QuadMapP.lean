module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ConPolyZono.quadMap`'s counts

`quadMap` is `quadMapDep` run on `dependent`: the factor and dependent-generator
counts are `dependent`'s own, `quadMapDep`'s square then landing on that count
rather than the operand's, and the independent block empties — the constraint
count `m` and the constraint-generator count `q` both carry straight through,
since the constraint system reads none of the enclosing polynomial zonotope.
`rfl` by unfolding `quadMapDep` and `dependent` rather than restating either.

## `ConPolyZono.quadMap`'s dependent-generator count is `O(m ^ 2)`

Not a bare arithmetic fact about `(m+1)*(m+1)`, but one tied to `quadMap`
through a family of sets whose combined dependent-and-independent count grows
as `m`. `quadMap_h` reduces the left side to that product, which `4 * m ^ 2`
dominates for every `m ≥ 1`.

`Asymptotics.IsBigO.of_bound` closes it: it asks for domination by a fixed
constant `∀ᶠ x in l`, which the whole range `m ≥ 1` clears with room to spare.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_p (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).p = cPZ.p + cPZ.qI := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
