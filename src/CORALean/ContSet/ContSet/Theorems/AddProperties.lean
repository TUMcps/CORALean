import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# What a Minkowski sum does to emptiness, degeneracy and boundedness

[1, Table 1 (⊕)], the cells that hold: a sum with `∅` is `∅`; a nonempty summand carries the
other's interior and unboundedness over; bounded plus bounded is bounded. The table also claims
"degenerate ⊕ non-degenerate is non-degenerate", "degenerate ⊕ unbounded is unbounded",
"non-degenerate ⊕ bounded is non-degenerate" and "bounded ⊕ unbounded is unbounded", which the
paper's own convention — `∅` is degenerate and bounded — refutes
(`add_properties_counterexample`); each holds once the first summand is nonempty, which is the
third and fourth clause here.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem add_properties (S₁ S₂ : Set (Vec ℝ n)) :
    (S₁ = ∅ → S₁ + S₂ = ∅) ∧ (S₁.Nonempty → S₂.Nonempty → (S₁ + S₂).Nonempty) ∧
      (S₁.Nonempty → (interior S₂).Nonempty → (interior (S₁ + S₂)).Nonempty) ∧
      (S₁.Nonempty → ¬ Bornology.IsBounded S₂ → ¬ Bornology.IsBounded (S₁ + S₂)) ∧
      (Bornology.IsBounded S₁ → Bornology.IsBounded S₂ →
        Bornology.IsBounded (S₁ + S₂)) := by -- --- PROOF ---
  refine ⟨fun h => by rw [h, Set.empty_add], fun h₁ h₂ => h₁.add h₂, fun h₁ h₂ => ?_,
    fun ⟨s, hs⟩ hnb hb => hnb ?_, fun h₁ h₂ => h₁.add h₂⟩
  -- `S₁ + interior S₂` is open and inside the sum
  · exact (h₁.add h₂).mono (interior_maximal (Set.add_subset_add_left interior_subset)
      (IsOpen.add_left isOpen_interior))
  -- `S₂` is a translate of a part of the sum
  · have hsub : S₂ ⊆ {-s} + ({s} + S₂) := fun x hx =>
      ⟨-s, rfl, s + x, ⟨s, rfl, x, hx, rfl⟩, neg_add_cancel_left s x⟩
    exact (Bornology.isBounded_singleton.add (hb.subset
      (Set.add_subset_add_right (Set.singleton_subset_iff.mpr hs)))).subset hsub

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
