module

public import CORALean.ContDynamics.NonlinearSys.Definitions.CancelRedundant
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-!
# A cancelled segment lies in the polytopes of the past steps

[1, Sec. VI-B]: whatever `cancelRedundant` drops, the polytope enclosure of the dropped
segment is inside the union of the polytopes of the past `ζ` steps, so every point of every
current segment is in a kept segment or in an enclosure of a past one. This is the whole of
what the check says: the dropped segment is "reached before" only up to those enclosures.

## Inputs
* `seg` – segment set
* `poly` – polytope enclosure
* `δ` – cancellation period
* `ζ` – history length
* `k` – step number
* `hist` – past segments
* `segs` – current segments

## Hypotheses
* `hpoly` – polytope encloses segment

## Conclusion
* every segment point is kept or in a past polytope

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". 2008 47th IEEE Conference on Decision
      and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {β : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of a segment `seg s ⊆ poly s` is in a kept segment or in a past polytope. -/
theorem NonlinearSys.cancelRedundant_covers (seg poly : β → Set (Vec ℝ n))
    (hpoly : ∀ s, seg s ⊆ poly s) (δ ζ k : ℕ) (hist : List (List β))
    (segs : List β) : -- --- CONCL ---
    ⋃ s ∈ segs, seg s ⊆ (⋃ s ∈ NonlinearSys.cancelRedundant poly δ ζ k hist segs, seg s)
      ∪ ⋃ t ∈ hist.take ζ, ⋃ s' ∈ t, poly s' := by -- --- PROOF ---
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  unfold NonlinearSys.cancelRedundant
  split_ifs with hδ
  · -- dropped means an empty difference, so the polytope is inside the past ones
    by_cases hkeep : ¬ (poly s \ ⋃ t ∈ hist.take ζ, ⋃ s' ∈ t, poly s') = ∅
    · left
      simp only [Set.mem_iUnion]
      exact ⟨s, List.mem_filter.mpr ⟨hs, by simp [hkeep]⟩, hxs⟩
    · right
      have hsub : poly s ⊆ ⋃ t ∈ hist.take ζ, ⋃ s' ∈ t, poly s' := by
        rw [not_not, Set.sdiff_eq_empty] at hkeep
        exact hkeep
      exact hsub (hpoly s hxs)
  · left
    simp only [Set.mem_iUnion]
    exact ⟨s, hs, hxs⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
