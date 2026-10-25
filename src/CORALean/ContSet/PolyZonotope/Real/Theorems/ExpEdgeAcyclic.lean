module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IsExpEdge
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The generator graph has no cycles

`[1, Lemma 1]`. `[1]` argues it one index at a time (the `k`-th exponent cannot increase along
a path), which has to track an index that changes from edge to edge. One `ℕ`-valued measure
does the same work: an edge holds the two columns equal off `k₀` and strictly lowers the
exponent there, so the *column sum* `∑ k, E k i` strictly drops across every edge. Acyclicity
is then irreflexivity of `<` on ℕ. The parity condition and the threshold only shrink the edge
set. Stated as `¬ Relation.TransGen`, "no cycles" literally; well-foundedness of the reversed
relation follows from the same measure.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `η` – exponent threshold
* `i` – generator index

## Hypotheses
* none

## Conclusion
* no chain of relaxable edges returns to its start

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The column sum strictly drops across an edge: every other exponent is
shared, and the one the edge moves falls. -/
theorem PolyZonotope.aux_sum_lt_of_expEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) {η : ℕ}
    {i j : Fin h} (hij : PolyZonotope.IsExpEdge E η i j) : -- --- CONCL ---
    ∑ k, E k j < ∑ k, E k i := by -- --- PROOF ---
  obtain ⟨k₀, hsim, -, -, hlt⟩ := hij
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ k₀, hlt⟩
  by_cases hk : k = k₀
  · subst hk
    exact le_of_lt hlt
  · exact le_of_eq (hsim k hk).symm

/-- The same along a path, the measure dropping at every step. -/
theorem PolyZonotope.aux_sum_lt_of_path {p h : ℕ} (E : Fin p → Fin h → ℕ) {η : ℕ}
    {i j : Fin h} (hij : Relation.TransGen (PolyZonotope.IsExpEdge E η) i j) :
    ∑ k, E k j < ∑ k, E k i := by
  induction hij with
  | single hedge => exact PolyZonotope.aux_sum_lt_of_expEdge E hedge
  | tail _ hedge ih => exact lt_trans (PolyZonotope.aux_sum_lt_of_expEdge E hedge) ih


-- =======================================  MAIN THEOREM  ======================================= --

/-- The generator graph has no cycles: a path from a node back to itself would
put its column sum below itself. -/
theorem PolyZonotope.expEdge_acyclic {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (i : Fin h) :
    ¬ Relation.TransGen (PolyZonotope.IsExpEdge E η) i i :=
  fun hi => lt_irrefl _ (PolyZonotope.aux_sum_lt_of_path E hi)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
