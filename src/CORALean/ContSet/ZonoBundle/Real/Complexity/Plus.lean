import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Complexity.Plus

/-!
# `ZonoBundle.plus`'s counts

`plus`'s bundle size: every zonotope of one bundle paired with every zonotope
of the other, so the count multiplies rather than adds — the reason it, not
`and`, carries this directory's `O`-notation statement, in `PlusBigO.lean`.

The second-order count also comes out cleanly: each paired component is
`Zonotope.plus` of the two it came from, so its own generator count is theirs
added, by `Zonotope.plus_h`. `rfl` against both structure instances.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ZonoBundle.plus_k (zB₁ zB₂ : ZonoBundle α) : (zB₁.plus zB₂).k = zB₁.k * zB₂.k := rfl

omit [Module ℝ α] in
theorem ZonoBundle.plus_Z_h (zB₁ zB₂ : ZonoBundle α) (p : Fin (zB₁.k * zB₂.k)) :
    ((zB₁.plus zB₂).Z p).h =
      (zB₁.Z (finProdFinEquiv.symm p).1).h + (zB₂.Z (finProdFinEquiv.symm p).2).h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
