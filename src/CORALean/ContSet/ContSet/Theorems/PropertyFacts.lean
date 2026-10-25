module

public import CORALean.ContSet.ContSet.Theorems.ProdProperties

@[expose] public section

/-!
# The set properties CORA stores, and how they combine

[1, Sec. 3]: empty sets are bounded and degenerate, non-degenerate and unbounded sets are
nonempty, and properties combine pair by pair: the product of a nonempty set and a degenerate,
unbounded one is degenerate and unbounded, from the cells "NE × D = D" and "NE × NB = NB". The
third convention, that `∅` is in minimal representation, is about CORA's storage, not the set.

## Inputs
* `S` – set
* `S₁` – set
* `S₂` – set

## Hypotheses
* none

## Conclusion
* basic facts on boundedness, interior and emptiness of sets and products

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

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem property_facts (S : Set (Vec ℝ n₁)) (S₁ : Set (Vec ℝ n₁))
    (S₂ : Set (Vec ℝ n₂)) : -- --- CONCL ---
    Bornology.IsBounded (∅ : Set (Vec ℝ n₁)) ∧ interior (∅ : Set (Vec ℝ n₁)) = ∅ ∧
      ((interior S).Nonempty → S.Nonempty) ∧ (¬ Bornology.IsBounded S → S.Nonempty) ∧
      (S₁.Nonempty → interior S₂ = ∅ → ¬ Bornology.IsBounded S₂ →
        interior (S₁ ×ˢ S₂) = ∅ ∧ ¬ Bornology.IsBounded (S₁ ×ˢ S₂)) := by -- --- PROOF ---
  refine ⟨Bornology.isBounded_empty, interior_empty, fun h => h.mono interior_subset,
    fun h => Set.nonempty_iff_ne_empty.mpr fun he => h (he ▸ Bornology.isBounded_empty),
    fun h₁ hd hnb => ⟨(prod_properties S₁ S₂).2.2.1 (Or.inr hd),
      (prod_properties S₁ S₂).2.2.2.2.1 h₁ hnb⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
