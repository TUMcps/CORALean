module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHullCora
public import CORALean.ContSet.Capsule.Real.Theorems.Convex
public import CORALean.ContSet.Capsule.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# CORA's `capsule/convHull_` errors on an empty second operand

The branch for an empty `S` (l. 57-59 of `@capsule/convHull_.m`) executes `return` without having
set `S_out`, so `convHull(C, capsule.empty(n))` raises MATLAB's "output argument not assigned"
error, where the hull of a convex set with `∅` is the set itself. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `S = capsule.empty n` CORA's `convHull_` returns no value, while the hull is `C`. -/
theorem Capsule.convHull_empty_cora_crash (C : Capsule n) :
    C.convHullCora (Capsule.empty n) = none ∧
      convexHull ℝ (C.construct ∪ (Capsule.empty n).construct) = C.construct := by
  refine ⟨by simp [Capsule.convHullCora, Capsule.empty], ?_⟩
  rw [Capsule.empty_exact, Set.union_empty]
  exact (Capsule.convex_construct C).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
