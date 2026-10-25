module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# What an intersection does to emptiness, degeneracy and boundedness

[1, Table 1 (∩)]: intersecting with an empty, a degenerate or a bounded set leaves an empty, a
degenerate or a bounded set, and nothing more is claimed. Every cell holds; the other operand's
cells follow by commutativity.

## Inputs
* `S₁` – set
* `S₂` – set

## Hypotheses
* none

## Conclusion
* emptiness, empty interior and boundedness of `S₁` pass to `S₁ ∩ S₂`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem inter_properties (S₁ S₂ : Set (Vec ℝ n)) :
    (S₁ = ∅ → S₁ ∩ S₂ = ∅) ∧ (interior S₁ = ∅ → interior (S₁ ∩ S₂) = ∅) ∧
      (Bornology.IsBounded S₁ → Bornology.IsBounded (S₁ ∩ S₂)) := by
  refine ⟨fun h => by rw [h, Set.empty_inter], fun h => ?_, fun h => h.subset Set.inter_subset_left⟩
  rw [← Set.subset_empty_iff, ← h]
  exact interior_mono Set.inter_subset_left

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
