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

theorem PolyZonotope.linComb_p (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).p = pZ₁.p + pZ₂.p + 1 := rfl

theorem PolyZonotope.linComb_h (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).h = pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1) := rfl

theorem PolyZonotope.linComb_q (pZ₁ pZ₂ : PolyZonotope α) :
    (pZ₁.linComb pZ₂).q = pZ₁.q + pZ₂.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
