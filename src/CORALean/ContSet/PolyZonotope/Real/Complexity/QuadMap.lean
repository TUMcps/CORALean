import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `PolyZonotope.quadMap`'s counts

`quadMap` is `bilin` at `quadBilin`, one set paired with itself, run on
`dependent` first: the factor count and dependent-generator count are
`dependent`'s own, `bilin`'s square then landing on `dependent`'s count rather
than the operand's, and the independent block is again empty. `rfl` by
unfolding `quadMapDep` rather than restating `bilin_h`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.quadMap_p (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q PZ).p = PZ.p + PZ.q := rfl

theorem PolyZonotope.quadMap_h (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q PZ).h = (PZ.h + PZ.q + 1) * (PZ.h + PZ.q + 1) := rfl

theorem PolyZonotope.quadMap_q (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q PZ).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
