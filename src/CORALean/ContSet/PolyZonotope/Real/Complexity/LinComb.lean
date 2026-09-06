import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

/-!
# `PolyZonotope.linComb`'s counts

One fresh factor over the two operands' own, dependent generators tripled in
the two doubled blocks plus the one fresh centre-difference generator, and the
independent block carried over at its combined count. `rfl` against the
structure instance in `Operations/LinComb.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_p (PZ₁ PZ₂ : PolyZonotope α) :
    (PZ₁.linComb PZ₂).p = PZ₁.p + PZ₂.p + 1 := rfl

theorem PolyZonotope.linComb_h (PZ₁ PZ₂ : PolyZonotope α) :
    (PZ₁.linComb PZ₂).h = PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1) := rfl

theorem PolyZonotope.linComb_q (PZ₁ PZ₂ : PolyZonotope α) :
    (PZ₁.linComb PZ₂).q = PZ₁.q + PZ₂.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
