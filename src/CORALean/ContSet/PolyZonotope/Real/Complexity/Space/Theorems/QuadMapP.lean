module

public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

@[expose] public section

/-!
# `PolyZonotope.quadMap`'s counts

`quadMap` is `bilin` at `quadBilin`, one set paired with itself, run on
`dependent` first: the factor count and dependent-generator count are
`dependent`'s own, `bilin`'s square then landing on `dependent`'s count rather
than the operand's, and the independent block is again empty. `rfl` by
unfolding `quadMapDep` rather than restating `bilin_h`.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the factor count is dependent plus independent generators
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `quadMap`'s result. -/
theorem PolyZonotope.quadMap_p (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.quadMap Q pZ).p = pZ.p + pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
