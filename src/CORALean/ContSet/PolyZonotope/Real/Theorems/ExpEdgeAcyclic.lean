import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge

/-!
# The generator graph has no cycles

`[1, Lemma 1]`. `[1]` argues it one index at a time — the `k`-th exponent cannot
increase along a path — which has to keep track of an index that changes from
edge to edge. One `ℕ`-valued measure does the same work: an edge holds the two
columns equal off `k₀` and strictly lowers the exponent there, so the *column
sum* `∑ k, E k i` strictly drops across every edge, whichever index it moves.
Acyclicity is then irreflexivity of `<` on ℕ.

The parity condition and the threshold only shrink the edge set, so they cost
this nothing: they are what bounds `eDiff`, not what orders the nodes.

Stated as `¬ Relation.TransGen`, which is "no cycles" literally — a cycle is a
non-empty path from a node back to itself — and is what a caller ruling out a
merge that comes round again would ask for. Well-foundedness of the reversed
relation follows from the same measure, and belongs to whatever first recurses
along the graph rather than here.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The column sum strictly drops across an edge: every other exponent is
shared, and the one the edge moves falls. -/
theorem PolyZonotope.aux_sum_lt_of_expEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) {η : ℕ}
    {i j
      : Fin h} (hij : PolyZonotope.ExpEdge E η i j) : ∑ k, E k j < ∑ k, E k i := by -- --- PROOF ---
  obtain ⟨k₀, hsim, -, -, hlt⟩ := hij
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ k₀, hlt⟩
  by_cases hk : k = k₀
  · subst hk
    exact le_of_lt hlt
  · exact le_of_eq (hsim k hk).symm

/-- The same along a path, the measure dropping at every step. -/
theorem PolyZonotope.aux_sum_lt_of_path {p h : ℕ} (E : Fin p → Fin h → ℕ) {η : ℕ}
    {i j : Fin h} (hij : Relation.TransGen (PolyZonotope.ExpEdge E η) i j) :
    ∑ k, E k j < ∑ k, E k i := by -- --- PROOF ---
  induction hij with
  | single hedge => exact PolyZonotope.aux_sum_lt_of_expEdge E hedge
  | tail _ hedge ih => exact lt_trans (PolyZonotope.aux_sum_lt_of_expEdge E hedge) ih


-- =======================================  MAIN THEOREM  ======================================= --

/-- The generator graph has no cycles: a path from a node back to itself would
put its column sum below itself. -/
theorem PolyZonotope.expEdge_acyclic {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (i : Fin h) :
    ¬ Relation.TransGen (PolyZonotope.ExpEdge E η) i i :=
  fun hi => lt_irrefl _ (PolyZonotope.aux_sum_lt_of_path E hi)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
