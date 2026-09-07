import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy

/-!
# `Zonotope.reduceBy_h`

`reduceBy`'s generator count: the kept block, `q`, plus one absorbing
generator per output coordinate, `n` — never smaller than `n`, however small
`q` is chosen. `Theorems/ReduceOrder.lean` turns this into a bound on the
reduction order. `rfl`, since `Operations/ReduceBy.lean` states `h` directly.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceBy_h (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.reduceBy part).h = q + n := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
