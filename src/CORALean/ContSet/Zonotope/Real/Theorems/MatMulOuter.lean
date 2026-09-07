import CORALean.ContSet.Zonotope.Real.Operations.MatMul
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter

/-!
# A product of two matrix zonotopes over-approximates every product it denotes

`bilin_outer` at `matMulBilin`, whose application is `*` by `rfl`
(`matMulBilin_apply`) — so the two unions of images are literally the same set
and the statement is `bilin_outer`'s, with nothing to rewrite.

The enclosure is strict in general: the cross generators are free, so a product
of two matrix zonotopes holds pairs the two never take together.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMul_outer (M : Zonotope (Mat ℝ p q)) (N : Zonotope (Mat ℝ q r)) :
    (⋃ A ∈ M.construct, (A * ·) '' N.construct) ⊆ (Zonotope.matMul M N).construct :=
  Zonotope.bilin_outer matMulBilin M N

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
