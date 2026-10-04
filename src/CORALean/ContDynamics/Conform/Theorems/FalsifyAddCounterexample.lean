import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# [1, Sec. 2.2]'s falsification test `y ∉ R ⊕ V` falsifies conformant measurements

[1, Sec. 2.2] reduces the falsification `(y ⊕ V) ∩ R = ∅` to `y ∉ R ⊕ V`. For an
asymmetric error set the two differ: in one dimension, `R = {0}`, `V = [0, 1]`, the
measurement `y = -1` has `y ⊕ V = [-1, 0] ∋ 0`, so the exact output may be reachable,
yet `-1 ∉ R ⊕ V = [0, 1]` declares it falsified. The test is `y ∉ R ⊕ (-V)`
(`DisjointSingletonAddIff`); for a centrally symmetric `V` both coincide.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 2.2]'s `y ∉ R ⊕ V` holds at a measurement that does not falsify. -/
theorem Conform.falsify_add_counterexample :
    ∃ (R V : Set ℝ) (y : ℝ), ¬ Disjoint ({y} + V) R ∧ y ∉ R + V := by -- --- PROOF ---
  refine ⟨{0}, Set.Icc 0 1, -1, fun h => ?_, ?_⟩
  · -- `-1 + 1 = 0` is a possible exact output
    exact Set.disjoint_left.mp h ⟨-1, rfl, 1, ⟨by norm_num, le_rfl⟩, by norm_num⟩ rfl
  · rintro ⟨r, hr, v, ⟨hv, -⟩, hsum⟩
    rw [Set.mem_singleton_iff] at hr
    subst hr
    simp only at hsum
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
