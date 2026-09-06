import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter

/-!
# A matrix zonotope's product over-approximates every matrix it denotes

`bilin_outer` at `Matrix.mulVecBilin ℝ ℝ`, whose application is `*ᵥ` by `rfl`
(`Matrix.mulVecBilin_apply`) — so the two unions of images are the same set,
matched pointwise rather than rewritten.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesMatZonotope_outer (M : Zonotope (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (⋃ A ∈ M.construct, (A *ᵥ ·) '' Z.construct)
      ⊆ (Zonotope.mtimesMatZonotope M Z).construct := by
  -- `h` first, with no expected type: against the goal directly its module instances time out
  have h := Zonotope.bilin_outer (Matrix.mulVecBilin ℝ ℝ) M Z
  simp only [← Matrix.mulVecBilin_apply ℝ ℝ]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
