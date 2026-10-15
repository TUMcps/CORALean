module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConPolyZono.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·`: it touches the centre and both generator blocks
only, so all five counts carry over exactly — the constraint system in
particular is untouched, since `M` never reaches `A`, `b` or `R`. `rfl`
against the structure instance in `Operations/Mtimes.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `mtimes`'s result. -/
theorem ConPolyZono.mtimes_p (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).p = cPZ.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
