import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin

/-!
# `PolyZonotope.bilin`'s counts

The shared factor count carries over from either operand, since sharing is a
hypothesis rather than a fresh count; the dependent generator count is the two
operands' own plus their cross block, `(h₁+1)*(h₂+1)` — quadratic, not linear;
and the independent block is empty, `bilin` being a claim about `point`.
`BilinBigO.lean` puts the quadratic one in `O`-notation. `rfl` against the
structure instance in `Operations/Bilin.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.bilin_p (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : (PolyZonotope.bilin f pZ₁ pZ₂ hp).p = pZ₁.p := rfl

theorem PolyZonotope.bilin_h (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) :
    (PolyZonotope.bilin f pZ₁ pZ₂ hp).h = (pZ₁.h + 1) * (pZ₂.h + 1) := rfl

theorem PolyZonotope.bilin_q (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : (PolyZonotope.bilin f pZ₁ pZ₂ hp).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
