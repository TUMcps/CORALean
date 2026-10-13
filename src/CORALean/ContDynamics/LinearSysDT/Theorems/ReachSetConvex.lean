module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# `reachSet` is convex

Induction on `k`, the step being a linear image — convex by `Convex.linear_image`
— summed with `construct U` by `Convex.add`. Neither needs continuity, so this
sits beside `ReachSetOuter`: no operation class in sight, and no topology either.

This is the missing hypothesis `minkowskiDiff_inner_of_outer` asks of the exact
set it turns into an inner approximation; `ReachSetIsCompact` supplies the other.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact set reached in `k` steps is convex whenever the initial and input
sets are. -/
theorem LinearSysDT.reachSet_convex (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    (hR₀ : Convex ℝ (construct R₀)) (hU : Convex ℝ (construct U)) (k : ℕ) :
    Convex ℝ (sys.reachSet R₀ U k) := by -- --- PROOF ---
  induction k with
  | zero => exact hR₀
  | succ k ih =>
    show Convex ℝ (mulVecLin (toRealMat sys.A) '' sys.reachSet R₀ U k + construct U)
    exact (ih.linear_image (mulVecLin (toRealMat sys.A))).add hU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
