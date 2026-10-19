module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Bornology.Constructions

@[expose] public section

/-!
# What a Cartesian product does to emptiness, degeneracy and boundedness

[1, Table 1 (×)], the cells that hold. The paper stacks `[s₁; s₂] ∈ ℝ^{n₁+n₂}`; the product
type is the same space up to a linear homeomorphism, and is what Mathlib's interiors and
bornologies are stated for. The table also claims "D × B = D, B" and "D × NB = D, NB": a line
times a point is unbounded, and `∅ × ℝⁿ` is bounded (`prod_properties_counterexample`). A
degenerate factor makes the product degenerate, and a nonempty factor carries the other's
unboundedness, which is all that survives.

## Inputs
* `S₁` – first set
* `S₂` – second set

## Hypotheses
* none

## Conclusion
* emptiness, interior and boundedness of `S₁ × S₂` follow from those of the factors

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem prod_properties (S₁ : Set (Vec ℝ n₁)) (S₂ : Set (Vec ℝ n₂)) : -- --- CONCL ---
    (S₁ = ∅ ∨ S₂ = ∅ → S₁ ×ˢ S₂ = ∅) ∧ (S₁.Nonempty → S₂.Nonempty → (S₁ ×ˢ S₂).Nonempty) ∧
      (interior S₁ = ∅ ∨ interior S₂ = ∅ → interior (S₁ ×ˢ S₂) = ∅) ∧
      ((interior S₁).Nonempty → (interior S₂).Nonempty → (interior (S₁ ×ˢ S₂)).Nonempty) ∧
      (S₁.Nonempty → ¬ Bornology.IsBounded S₂ → ¬ Bornology.IsBounded (S₁ ×ˢ S₂)) ∧
      (¬ Bornology.IsBounded S₁ → S₂.Nonempty → ¬ Bornology.IsBounded (S₁ ×ˢ S₂)) ∧
      (Bornology.IsBounded S₁ → Bornology.IsBounded S₂ →
        Bornology.IsBounded (S₁ ×ˢ S₂)) := by -- --- PROOF ---
  refine ⟨Set.prod_eq_empty_iff.mpr, fun h₁ h₂ => h₁.prod h₂, fun h => ?_,
    fun h₁ h₂ => ?_, fun h₁ h₂ hb => h₂ ?_, fun h₁ h₂ hb => h₁ ?_, fun h₁ h₂ => h₁.prod h₂⟩
  · rw [interior_prod_eq]
    exact Set.prod_eq_empty_iff.mpr h
  · rw [interior_prod_eq]
    exact h₁.prod h₂
  -- a bounded product of nonempty factors has bounded factors
  · rcases Bornology.isBounded_prod.mp hb with h | h | h
    · exact absurd h h₁.ne_empty
    · rw [h]
      exact Bornology.isBounded_empty
    · exact h.2
  · rcases Bornology.isBounded_prod.mp hb with h | h | h
    · rw [h]
      exact Bornology.isBounded_empty
    · exact absurd h h₂.ne_empty
    · exact h.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
