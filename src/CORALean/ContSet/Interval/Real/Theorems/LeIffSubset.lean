module

public import CORALean.ContSet.Interval.Real.Theorems.LeSubset
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# `Interval.le` is exactly containment of a nonempty box

The converse of `le_subset`: a nonempty `I` has `inf` and `sup` as members, and containment puts
them in `J`. For an empty `I` the inclusion is trivial and `le` need not hold, so the hypothesis
is needed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.le_iff_subset {I J : Interval α} (hI : I.IsNonempty) :
    I.le J ↔ I.construct ⊆ J.construct := by
  refine ⟨Interval.le_subset, fun h i => ?_⟩
  have h₁ : I.inf ∈ J.construct := h fun j => ⟨le_refl _, hI j⟩
  have h₂ : I.sup ∈ J.construct := h fun j => ⟨hI j, le_refl _⟩
  exact ⟨(h₁ i).1, (h₂ i).2⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
