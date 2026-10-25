module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# What a Minkowski difference does to emptiness, degeneracy and boundedness

[1, Table 1 (⊖)] with `S₁ ⊖ S₂ = {s | s ⊕ S₂ ⊆ S₁}` [1, Table 3]: subtracting `∅` gives the
whole space; a nonempty subtrahend from `∅` gives `∅`; a non-degenerate one from a degenerate set
gives `∅`; a nonempty one from a bounded set leaves it bounded; an unbounded one from a bounded
set gives `∅`. The table also has "E ⊖ D = E", "E ⊖ B = E", "B ⊖ D = B" and "B ⊖ B = B", which
fail at a subtrahend `∅` — degenerate and bounded by the paper's convention
(`minkowskiDiff_properties_counterexample`); with a nonempty subtrahend they are the second and
fourth clause.

## Inputs
* `S₁` – minuend
* `S₂` – subtrahend

## Hypotheses
* none

## Conclusion
* emptiness, interior and boundedness of `S₁ ⊖ S₂` follow from those of the operands

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

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem minkowskiDiff_properties (S₁ S₂ : Set (Vec ℝ n)) : -- --- CONCL ---
    (S₂ = ∅ → minkowskiDiff S₁ S₂ = Set.univ ∧
        (0 < n → ¬ Bornology.IsBounded (minkowskiDiff S₁ S₂))) ∧
      (S₁ = ∅ → S₂.Nonempty → minkowskiDiff S₁ S₂ = ∅) ∧
      (interior S₁ = ∅ → (interior S₂).Nonempty → minkowskiDiff S₁ S₂ = ∅) ∧
      (Bornology.IsBounded S₁ → S₂.Nonempty → Bornology.IsBounded (minkowskiDiff S₁ S₂)) ∧
      (Bornology.IsBounded S₁ → ¬ Bornology.IsBounded S₂ → minkowskiDiff S₁ S₂ =
      ∅) := by -- --- PROOF ---
  -- a point of the difference carries a translate of `S₂` into `S₁`
  have htr : ∀ x ∈ minkowskiDiff S₁ S₂, x +ᵥ S₂ ⊆ S₁ := fun x hx =>
    Set.vadd_set_subset_iff.mpr fun y hy => hx y hy
  have huniv : S₂ = ∅ → minkowskiDiff S₁ S₂ = Set.univ := fun h =>
    Set.eq_univ_of_forall fun x y hy => by rw [h] at hy; exact hy.elim
  refine ⟨fun h => ⟨huniv h, fun hn => ?_⟩, fun h₁ ⟨y, hy⟩ => ?_, fun h₁ h₂ => ?_,
    fun hb ⟨y, hy⟩ => ?_, fun hb hnb => ?_⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [huniv h]
    exact NormedSpace.unbounded_univ ℝ _
  · exact Set.eq_empty_of_forall_notMem fun x hx => by
      have := hx y hy
      rw [h₁] at this
      exact this
  -- a translate of a set with interior inside a set without
  · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hint := interior_mono (htr x hx)
    rw [interior_vadd, h₁] at hint
    obtain ⟨z, hz⟩ := h₂
    exact hint (Set.vadd_mem_vadd_set hz)
  -- the difference lies in `S₁ - y`
  · refine (hb.add (Bornology.isBounded_singleton (x := -y))).subset fun x hx =>
      ⟨x + y, hx y hy, -y, rfl, add_neg_cancel_right x y⟩
  · refine Set.eq_empty_of_forall_notMem fun x hx => hnb ?_
    refine (Bornology.isBounded_singleton (x := -x)).add hb |>.subset fun y hy =>
      ⟨-x, rfl, x + y, hx y hy, neg_add_cancel_left x y⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
