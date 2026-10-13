import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# The reduced error contains the unreduced one

The two recursions share their step's box and differ only in the `reduce` on
top, so the induction is one application of `reduce_outer` per step with
`plus_exact` and `mtimes_exact` splitting what is under it — the previous
step's error rides through the same `A` on both sides.

This is the fact that makes `reachErrorReduced` worth having rather than a
second definition sitting beside the first: everything already proved about
`reachError` transfers to it in the direction the error is used, since the
error is *added* to the exact set. `reach_subset_reachSet_add_errorReduced` is
that transfer, and `reachInnerReduced_subset_reachInner` is the price paid for
it, read on the other side of the Minkowski difference.

`contains` and not `_outer`: both sides are computed errors, neither is the
exact set, and the name reads with the receiver elided.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reducing the error only grows it: every point the unreduced recursion owes
is owed by the reduced one too. -/
theorem LinearSysDT.reachErrorReduced_contains_reachError (sys : LinearSysDT ℝ n) {o : ℕ}
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
      ⊆ (sys.reachErrorReduced ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    -- the step's own box is the same on both sides; only what is carried differs
    set B := Zonotope.reduceBox
      ((Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) o
    have hl : sys.reachError ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = (Zonotope.mtimes sys.A (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus B := rfl
    have hr : sys.reachErrorReduced ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = Zonotope.reduce
            ((Zonotope.mtimes sys.A (sys.reachErrorReduced ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus B) o := rfl
    rw [hl, hr]
    -- `reduce` only grows what it is given, so it comes off first
    refine subset_trans ?_ (Zonotope.reduce_outer _ o)
    rw [← Zonotope.plus_exact, ← Zonotope.plus_exact]
    refine Set.add_subset_add_right ?_
    -- and the carried part is the induction hypothesis through this step's `A`
    rw [← Zonotope.mtimes_exact, ← Zonotope.mtimes_exact]
    exact Set.image_mono ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
