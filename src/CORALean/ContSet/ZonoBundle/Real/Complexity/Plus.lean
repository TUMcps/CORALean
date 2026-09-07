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
theorem ZonoBundle.plus_k (B₁ B₂ : ZonoBundle α) : (B₁.plus B₂).k = B₁.k * B₂.k := rfl

omit [Module ℝ α] in
theorem ZonoBundle.plus_Z_h (B₁ B₂ : ZonoBundle α) (p : Fin (B₁.k * B₂.k)) :
    ((B₁.plus B₂).Z p).h =
      (B₁.Z (finProdFinEquiv.symm p).1).h + (B₂.Z (finProdFinEquiv.symm p).2).h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
