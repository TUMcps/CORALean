import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

/-!
# `PolyZonotope.mul`'s counts

The shared factor count carries over from the left operand, since sharing is a
hypothesis rather than a fresh count; the dependent generator count is the two
operands' own plus their cross block, `(h₁+1)*(h₂+1)` — quadratic, not linear,
as at `bilin`; and the independent block is empty, `mul` being a claim about
`point`. `rfl` against the structure instance in `Operations/Mul.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mul_p (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.mul pZ₁ pZ₂ hp).p = pZ₁.p := rfl

theorem PolyZonotope.mul_h (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.mul pZ₁ pZ₂ hp).h = (pZ₁.h + 1) * (pZ₂.h + 1) := rfl

theorem PolyZonotope.mul_q (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.mul pZ₁ pZ₂ hp).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
