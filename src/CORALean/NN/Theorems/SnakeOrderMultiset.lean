module

public import CORALean.NN.Operations.SnakeOrder
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The spiral visits every entry once

As a multiset the spiral's list is the sum of the singletons of all entries of the matrix: a
rearrangement of the entries, none dropped, none repeated.

## Inputs
* `h` – number of rows
* `w` – number of columns
* `A` – matrix

## Hypotheses
* none

## Conclusion
* the spiral lists every entry exactly once
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Finset

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A list written by `List.ofFn` is the sum of its singletons. -/
private theorem aux_coe_ofFn {w : ℕ} (f : Fin w → α) : -- --- CONCL ---
    ((List.ofFn f : List α) : Multiset α) = ∑ j, ({f j} : Multiset α) := by -- --- PROOF ---
  induction w with
  | zero => simp
  | succ w ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← ih fun j => f j.succ]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem snakeOrder_coe (h w : ℕ) (A : Fin h → Fin w → α) : -- --- CONCL ---
    ((snakeOrder h w A : List α) : Multiset α) =
      ∑ p : Fin h × Fin w, ({A p.1 p.2} : Multiset α) := by -- --- PROOF ---
  match h, w, A with
  | 0, w, A => simp [snakeOrder]
  | h + 1, w, A =>
    rw [snakeOrder, ← Multiset.coe_add, snakeOrder_coe w h, aux_coe_ofFn]
    -- the rest, turned, sums to the rest: swap the two indices and reverse one
    have hturn : ∑ p : Fin w × Fin h, ({A p.2.succ p.1.rev} : Multiset α) =
        ∑ x : Fin h, ∑ y : Fin w, ({A x.succ y} : Multiset α) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
    rw [hturn, Fintype.sum_prod_type, Fin.sum_univ_succ]
termination_by h + w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
