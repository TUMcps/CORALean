module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReducedOrders
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

@[expose] public section

/-!
# The reduced error contains the unreduced one, at a per-step order

`reachErrorReduced_contains_reachError` at a per-step order sequence: the same
proof, `o (k + 1)` read off in place of the one fixed `o` — `reduce_outer`
needs no positivity hypothesis on the order it grows by, so the sequence costs
the argument nothing past that substitution.

What this buys is the same as the fixed-order fact does: `reachErrorOrders`'s
theorems, once it has any, transfer to `reachErrorReducedOrders` in the
direction the error is used, since the error is *added* to the exact set.

## Inputs
* `sys` – system
* `o` – orders per step
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – orders positive

## Conclusion
* the unreduced error lies in the reduced error at per-step orders
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

/-- Reducing the error only grows it, at any order sequence: every point the
unreduced recursion owes is owed by the reduced one too. -/
theorem LinearSysDT.reachErrorReducedOrders_contains_reachErrorOrders (sys : LinearSysDT ℝ n)
    {o : ℕ → ℕ} (ho : ∀ k, 0 < o k) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachErrorOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
      ⊆ (sys.reachErrorReducedOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    -- the step's own box is the same on both sides; only what is carried differs
    set B := Zonotope.reduceBox
      ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U) (o (k + 1))
    have hl : sys.reachErrorOrders ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = (Zonotope.mtimes sys.A (sys.reachErrorOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus B := rfl
    have hr : sys.reachErrorReducedOrders ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
        = Zonotope.reduce ((Zonotope.mtimes sys.A
            (sys.reachErrorReducedOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus B) (o (k + 1)) := rfl
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
