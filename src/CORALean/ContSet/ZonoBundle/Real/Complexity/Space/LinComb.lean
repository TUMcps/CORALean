import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Complexity.Space.LinComb

/-!
# `ZonoBundle.linComb`'s counts

`linComb`'s bundle size: every zonotope of one bundle paired with every
zonotope of the other, so the count multiplies exactly as `plus`'s does.

The second-order count also comes out cleanly: each paired component is
`Zonotope.linComb` of the two it came from, so its own generator count is
theirs added plus the one fresh generator, by `Zonotope.linComb_h`. `rfl`
against both structure instances.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.linComb_k (zB₁ zB₂ : ZonoBundle α) : (zB₁.linComb zB₂).k = zB₁.k * zB₂.k := rfl

theorem ZonoBundle.linComb_Z_h (zB₁ zB₂ : ZonoBundle α) (p : Fin (zB₁.k * zB₂.k)) :
    ((zB₁.linComb zB₂).Z p).h =
      (zB₁.Z (finProdFinEquiv.symm p).1).h + (zB₂.Z (finProdFinEquiv.symm p).2).h + 1 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
