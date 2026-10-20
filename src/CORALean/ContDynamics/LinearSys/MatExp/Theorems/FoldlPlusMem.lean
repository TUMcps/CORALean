module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import Mathlib.Data.List.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

/-!
# Adding enclosures one by one encloses the sum

The loops of `expm` add one enclosure per Taylor order to the accumulated interval matrix. A
point of the start and a point of every added enclosure sum to a point of the result: induction
on the length, peeling the last index with `List.range'_concat`, against `plus_outer`.

## Inputs
* `f` – term enclosures
* `x` – terms
* `s` – start index
* `m` – number of terms
* `acc` – initial enclosure
* `a` – initial member

## Hypotheses
* `hx` – each term lies in its enclosure
* `ha` – initial member lies in the initial enclosure

## Conclusion
* the fold of enclosures encloses the sum
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The left fold of `Interval.plus` over `f s, …, f (s + m - 1)` encloses `a + ∑ x (s + j)`. -/
theorem MatExp.foldl_plus_mem (f : ℕ → Interval (Mat ℝ n n)) (x : ℕ → Mat ℝ n n) (s m : ℕ)
    (hx : ∀ j, j < m → x (s + j) ∈ (f (s + j)).construct) {acc : Interval (Mat ℝ n n)}
    {a : Mat ℝ n n} (ha : a ∈ acc.construct) : -- --- CONCL ---
    a + ∑ j ∈ Finset.range m, x (s + j) ∈
      ((List.range' s m).foldl (fun e i => Interval.plus e (f i))
        acc).construct := by -- --- PROOF ---
  -- peel the last index off both the list and the sum
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    rw [List.range'_concat, one_mul, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc]
    exact Interval.plus_outer _ _
      (Set.add_mem_add (ih fun j hj => hx j (Nat.lt_succ_of_lt hj)) (hx m (Nat.lt_succ_self m)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
