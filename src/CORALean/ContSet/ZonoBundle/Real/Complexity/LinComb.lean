import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Complexity.LinComb

/-!
# `ZonoBundle.linComb`'s counts

`linComb`'s bundle size: every zonotope of one bundle paired with every
zonotope of the other, so the count multiplies exactly as `plus`'s does.

The second-order count also comes out cleanly: each paired component is
`Zonotope.linComb` of the two it came from, so its own generator count is
theirs added plus the one fresh generator, by `Zonotope.linComb_h`. `rfl`
against both structure instances.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.linComb_k (B₁ B₂ : ZonoBundle α) : (B₁.linComb B₂).k = B₁.k * B₂.k := rfl

theorem ZonoBundle.linComb_Z_h (B₁ B₂ : ZonoBundle α) (p : Fin (B₁.k * B₂.k)) :
    ((B₁.linComb B₂).Z p).h =
      (B₁.Z (finProdFinEquiv.symm p).1).h + (B₂.Z (finProdFinEquiv.symm p).2).h + 1 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
