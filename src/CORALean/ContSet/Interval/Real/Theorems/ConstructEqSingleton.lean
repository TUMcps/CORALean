module

public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# A box that is a single point has both bounds at it

A nonempty box contains its two bounds, so if the whole box is `{v}` both bounds are `v`.

## Inputs
* `I` – interval
* `v` – the point

## Hypotheses
* `h` – the interval is the single point `v`

## Conclusion
* both bounds equal the point
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

theorem Interval.inf_sup_of_construct_eq_singleton {I : Interval α} {v : α}
    (h : I.construct = {v}) : -- --- CONCL ---
    I.inf = v ∧ I.sup = v := by -- --- PROOF ---
  have hne : I.IsNonempty := (Interval.isNonempty_iff I).2 ⟨v, by rw [h]; rfl⟩
  have h₁ : I.inf ∈ I.construct := fun i => ⟨le_refl _, hne i⟩
  have h₂ : I.sup ∈ I.construct := fun i => ⟨hne i, le_refl _⟩
  rw [h] at h₁ h₂
  exact ⟨h₁, h₂⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
