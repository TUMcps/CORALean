import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

/-!
# `ConZonotope.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·` on the enclosed zonotope, with the constraints
carried along untouched: the generator count survives as a zonotope's does,
and the constraint counts survive because `P` itself is not rewritten at all.
`rfl` against the structure instance in `Operations/Mtimes.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mtimes_h (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M C).h = C.h := rfl

theorem ConZonotope.mtimes_P_m (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M C).P.m = C.P.m := rfl

theorem ConZonotope.mtimes_P_me (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) :
    (ConZonotope.mtimes M C).P.me = C.P.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
