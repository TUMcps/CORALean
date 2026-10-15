module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

@[expose] public section

/-!
# `PolyZonotope.linComb`'s counts

One fresh factor over the two operands' own, dependent generators tripled in
the two doubled blocks plus the one fresh center-difference generator, and the
independent block carried over at its combined count. `rfl` against the
structure instance in `Operations/LinComb.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `linComb`'s result. -/
theorem PolyZonotope.linComb_p (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).p = pZ₁.p + pZ₂.p + 1 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
