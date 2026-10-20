module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Theorems.PowMaxOrder

@[expose] public section

/-!
# An elementary function keeps the model's order

`taylor` sums `N + 1` scaled powers of `T - c`, each at the model's order, and adds a remainder
of order `0`; the larger order wins.

## Inputs
* `T` – Taylor model
* `g` – outer function
* `c` – center
* `D` – derivative bound

## Hypotheses
* none

## Conclusion
* the expansion keeps the model's order
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonempty sum of models of one order has that order. -/
theorem Taylm.aux_sum_maxOrder {m N : ℕ} (T : Fin (m + 1) → Taylm n)
    (hT : ∀ i, (T i).maxOrder = N) : -- --- CONCL ---
    (Taylm.sum T).maxOrder = N := by -- --- PROOF ---
  induction m with
  | zero => simp [Taylm.sum, Taylm.plus, hT 0]
  | succ m ih =>
    have := ih (fun i => T i.succ) fun i => hT _
    simp only [Taylm.sum, Taylm.plus] at this ⊢
    rw [this, hT 0, max_self]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.taylor_maxOrder (T : Taylm n) (g : ℝ → ℝ) (c D : ℝ) :
    (T.taylor g c D).maxOrder = T.maxOrder := by
  simp only [Taylm.taylor, Taylm.compose, Taylm.plus]
  rw [Taylm.aux_sum_maxOrder _ fun k => ?_]
  · exact Nat.max_zero _
  · simp [Taylm.smul, Taylm.pow_maxOrder, Taylm.minus, Taylm.plus, Taylm.uminus, Taylm.const]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
