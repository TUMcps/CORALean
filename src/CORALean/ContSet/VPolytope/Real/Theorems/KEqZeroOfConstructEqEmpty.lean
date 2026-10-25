module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# A V-representation of `∅` has no points

[1, Sec. 3 (minimal representation)]: "empty sets are ... in minimal representation". For points
this holds of every V-representation of `∅`: a V-polytope with a point contains it, so one
describing `∅` has none, the least count there is, and nothing to remove.

## Inputs
* `P` – polytope

## Hypotheses
* `hP` – `P` denotes the empty set

## Conclusion
* `P` has no vertices

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (minimal representation)]: a V-representation of `∅` lists no points. -/
theorem VPolytope.k_eq_zero_of_construct_eq_empty (P : VPolytope α)
    (hP : P.construct = ∅) : -- --- CONCL ---
    P.k = 0 := by -- --- PROOF ---
  by_contra hk
  -- the first point is a convex combination of the points, weight one on itself
  have hmem : P.V ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ P.construct :=
    ⟨Pi.single ⟨0, Nat.pos_of_ne_zero hk⟩ 1, fun j => by
      rw [Pi.single_apply]; split_ifs <;> norm_num, by simp, by simp [Pi.single_apply]⟩
  rw [hP] at hmem
  exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
