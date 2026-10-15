module

public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConZonotope.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·` on the enclosed zonotope, with the constraints
carried along untouched: the generator count survives as a zonotope's does,
and the constraint counts survive because `P` itself is not rewritten at all.
`rfl` against the structure instance in `Operations/Mtimes.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `mtimes`'s result. -/
theorem ConZonotope.mtimes_h (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M cZ).h = cZ.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
