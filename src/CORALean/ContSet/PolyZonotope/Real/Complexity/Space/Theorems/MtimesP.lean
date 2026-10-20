module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `PolyZonotope.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·`: all three counts carry over exactly, the index
types `Fin p`, `Fin h` and `Fin q` reused rather than grown or shrunk. `rfl`
against the structure instance in `Operations/Mtimes.lean`.

## Inputs
* `M` – matrix
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the factor count is preserved
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `mtimes`'s result. -/
theorem PolyZonotope.mtimes_p (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).p = pZ.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
