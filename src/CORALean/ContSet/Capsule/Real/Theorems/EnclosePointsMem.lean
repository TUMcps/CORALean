module

public import CORALean.ContSet.Capsule.Real.Operations.EnclosePoints

@[expose] public section

/-!
# `Capsule.enclosePoints` contains every point

Every `pts j` lies at the parameter `t = (d·g)/(g·g)` of the axis, at the distance `‖rej j‖₂`
from it, which the radius bounds. `|t| ≤ 1` because `‖d j‖₂ ≤ ‖g‖₂`, `g` being the longest `d`.
Outer only: the capsule is not the smallest, and CORA's own ball is larger still.

## Inputs
* `pts` – the points

## Hypotheses
* none

## Conclusion
* every point lies in `enclosePoints`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.range_subset_construct (pts : Fin N → Vec ℝ n) : -- --- CONCL ---
    Set.range pts ⊆ (Capsule.enclosePoints pts).construct := by -- --- PROOF ---
  rintro _ ⟨j, rfl⟩
  -- the two branches of `enclosePoints`: no points is impossible, `j` being one
  unfold Capsule.enclosePoints
  dsimp only
  split
  · rename_i h
    exact absurd (List.argmax_eq_none.mp h) (List.ne_nil_of_mem (List.mem_finRange j))
  · rename_i jm hm
    -- `g` is the longest `d`, so no point is farther from the center than `g`
    have hle := List.le_of_mem_argmax (List.mem_finRange j) hm
    set c : Vec ℝ n := (1 / (N : ℝ)) • ∑ j, pts j with hc
    set g : Vec ℝ n := pts jm - c with hg
    set d : Vec ℝ n := pts j - c with hd
    have hnd : ‖d‖₂ ≤ ‖g‖₂ := by
      rw [norm₂, norm₂]
      exact Real.sqrt_le_sqrt hle
    -- the parameter `t = (d·g)/(g·g)` of the projection onto the axis lies in `[-1, 1]`
    have hgg : g ⬝ᵥ g = ‖g‖₂ ^ 2 := dotProduct_self g
    have ht : |(d ⬝ᵥ g) / (g ⬝ᵥ g)| ≤ 1 := by
      rcases eq_or_ne g 0 with h0 | h0
      · simp [h0]
      · have hpos : 0 < ‖g‖₂ ^ 2 := by
          refine lt_of_le_of_ne (sq_nonneg _) fun h => h0 ?_
          have hs : ∑ i, g i ^ 2 = 0 := by rw [← norm₂_sq, ← h]
          ext i
          exact pow_eq_zero_iff (two_ne_zero) |>.mp
            ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hs i
              (Finset.mem_univ _))
        rw [hgg, abs_div, abs_of_pos hpos, div_le_one hpos]
        calc |d ⬝ᵥ g| ≤ ‖d‖₂ * ‖g‖₂ := abs_dotProduct_le_norm₂_mul_norm₂ d g
          _ ≤ ‖g‖₂ * ‖g‖₂ := mul_le_mul_of_nonneg_right hnd (norm₂_nonneg _)
          _ = ‖g‖₂ ^ 2 := (sq _).symm
    refine ⟨(d ⬝ᵥ g) / (g ⬝ᵥ g), abs_le.mp ht |> fun h => ⟨h.1, h.2⟩, ?_⟩
    -- the radius is a `max` over the list, so it bounds the entry of `j`
    have hfold : ∀ (l : List ℝ) (a : ℝ), a ∈ l → a ≤ l.foldr max 0 := by
      intro l a ha
      induction l with
      | nil => simp at ha
      | cons b l ih =>
        rcases List.mem_cons.mp ha with rfl | hl
        · exact le_max_left _ _
        · exact (ih hl).trans (le_max_right _ _)
    have hmem : ‖(pts j - c) - (((pts j - c) ⬝ᵥ g) / (g ⬝ᵥ g)) • g‖₂ ≤
        ((List.finRange N).map fun j =>
          ‖(pts j - c) - (((pts j - c) ⬝ᵥ g) / (g ⬝ᵥ g)) • g‖₂).foldr max 0 :=
      hfold _ _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    -- and the distance of `pts j` from the axis point is that entry
    have e : pts j - (c + ((d ⬝ᵥ g) / (g ⬝ᵥ g)) • g) = d - ((d ⬝ᵥ g) / (g ⬝ᵥ g)) • g := by
      rw [hd]; abel
    show ‖pts j - (c + ((d ⬝ᵥ g) / (g ⬝ᵥ g)) • g)‖₂ ≤ _
    rw [e]
    exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
