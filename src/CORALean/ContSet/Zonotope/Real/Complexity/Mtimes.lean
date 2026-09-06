import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `Zonotope.mtimes_h`

`mtimes` is `map` at `A *ᵥ ·`: the generator count carries over exactly, since
a linear image reuses the same index type `Fin h` rather than growing or
shrinking it. `rfl`, since `Operations/Mtimes.lean` states `h` directly.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimes_h (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimes M Z).h = Z.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
