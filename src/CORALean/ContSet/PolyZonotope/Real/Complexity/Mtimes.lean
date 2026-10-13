import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes

/-!
# `PolyZonotope.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·`: all three counts carry over exactly, the index
types `Fin p`, `Fin h` and `Fin q` reused rather than grown or shrunk. `rfl`
against the structure instance in `Operations/Mtimes.lean`.
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

theorem PolyZonotope.mtimes_p (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).p = pZ.p := rfl

theorem PolyZonotope.mtimes_h (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).h = pZ.h := rfl

theorem PolyZonotope.mtimes_q (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    (PolyZonotope.mtimes M pZ).q = pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
