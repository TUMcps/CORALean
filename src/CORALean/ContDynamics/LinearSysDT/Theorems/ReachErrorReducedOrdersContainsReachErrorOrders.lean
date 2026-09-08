import CORALean.ContDynamics.LinearSysDT.ReachErrorOrders
import CORALean.ContDynamics.LinearSysDT.ReachErrorReducedOrders
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# The reduced error contains the unreduced one, at a per-step order

`reachErrorReduced_contains_reachError` at a per-step order sequence: the same
proof, `o (k + 1)` read off in place of the one fixed `o` — `reduce_outer`
needs no positivity hypothesis on the order it grows by, so the sequence costs
the argument nothing past that substitution.

What this buys is the same as the fixed-order fact does: `reachErrorOrders`'s
theorems, once it has any, transfer to `reachErrorReducedOrders` in the
direction the error is used, since the error is *added* to the exact set.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reducing the error only grows it, at any order sequence: every point the
unreduced recursion owes is owed by the reduced one too. -/
theorem LinearSysDT.reachErrorReducedOrders_contains_reachErrorOrders (sys : LinearSysDT ℝ n)
    {o : ℕ → ℕ} (ho : ∀ k, 0 < o k) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachErrorOrders o ho R₀ U k).construct
      ⊆ (sys.reachErrorReducedOrders o ho R₀ U k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    -- the step's own box is the same on both sides; only what is carried differs
    set B := Zonotope.reduceBox
      ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) o ho R₀ U k)).plus U) (o (k + 1))
    have hl : sys.reachErrorOrders o ho R₀ U (k + 1)
        = (Zonotope.mtimes sys.A (sys.reachErrorOrders o ho R₀ U k)).plus B := rfl
    have hr : sys.reachErrorReducedOrders o ho R₀ U (k + 1)
        = Zonotope.reduce ((Zonotope.mtimes sys.A
            (sys.reachErrorReducedOrders o ho R₀ U k)).plus B) (o (k + 1)) := rfl
    rw [hl, hr]
    -- `reduce` only grows what it is given, so it comes off first
    refine subset_trans ?_ (Zonotope.reduce_outer _ (o (k + 1)))
    rw [← Zonotope.plus_exact, ← Zonotope.plus_exact]
    refine Set.add_subset_add_right ?_
    -- and the carried part is the induction hypothesis through this step's `A`
    rw [← Zonotope.mtimes_exact, ← Zonotope.mtimes_exact]
    exact Set.image_mono ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
