module

public import CORALean.ContSet.Interval.Real.Theorems.NormSubCenterLe
public import CORALean.ContSet.Interval.Real.Theorems.IntervalMatrixEq
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# `Interval.radius₂` is the radius of the smallest ball about the center

Every member is within `radius₂` of the center in `‖·‖₂` (`norm₂_sub_center_le`), and on a nonempty
box the corner `sup` is at exactly that distance (`aux_sup_sub_center`), so no smaller ball about
the center holds the box. It is the Euclidean ball about `center`; a ball about another point may be
smaller still. Nonemptiness is needed, as a crossed box has no corner to reach it.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – `I` nonempty

## Conclusion
* the radius norm is the least radius of a ball about the center containing the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The corner `sup` is `radius` from the center. -/
theorem Interval.aux_sup_sub_center (I : Interval (Vec ℝ n)) : I.sup - I.center = I.radius := by
  have h := Interval.center_add_radius I
  rw [← h]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.radius₂_isLeast {I : Interval (Vec ℝ n)} (hI : I.IsNonempty) : -- --- CONCL ---
    IsLeast {ρ : ℝ | construct I ⊆ {x | ‖x - I.center‖₂ ≤ ρ}}
      I.radius₂ := by -- --- PROOF ---
  refine ⟨fun x hx => Interval.norm₂_sub_center_le hx, fun ρ hρ => ?_⟩
  have hsup : I.sup ∈ construct I := fun i => ⟨hI i, le_refl _⟩
  have h : ‖I.sup - I.center‖₂ ≤ ρ := hρ hsup
  rw [Interval.aux_sup_sub_center] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
