import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap

/-!
# `ConPolyZono.quadMap`'s counts

`quadMap` is `quadMapDep` run on `dependent`: the factor and dependent-generator
counts are `dependent`'s own, `quadMapDep`'s square then landing on that count
rather than the operand's, and the independent block empties — the constraint
count `m` and the constraint-generator count `s` both carry straight through,
since the constraint system reads none of the enclosing polynomial zonotope.
`rfl` by unfolding `quadMapDep` and `dependent` rather than restating either.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMap_p (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).p = cPZ.p + cPZ.q := rfl

theorem ConPolyZono.quadMap_h (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).h = (cPZ.h + cPZ.q + 1) * (cPZ.h + cPZ.q + 1) := rfl

theorem ConPolyZono.quadMap_q (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).q = 0 := rfl

theorem ConPolyZono.quadMap_m (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).m = cPZ.m := rfl

theorem ConPolyZono.quadMap_s (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).s = cPZ.s := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
