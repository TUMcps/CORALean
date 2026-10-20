module

public import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe

@[expose] public section

/-!
# A point of a box is its center plus a multiple of its radius

Every `x` of a box is `center + β ⊙ radius` with `|β_i| ≤ 1`: the coefficients `[x] = mid([x]) ⊕
rad([x]) ⊗ [-1, 1]` leaves free, where a coordinate has width `0` taking `β_i = 0`. This is the
step from a box to the zonotope with one generator per coordinate.

## Inputs
* `I` – interval box
* `x` – point of the box

## Hypotheses
* `hx` – `x` lies in the box

## Conclusion
* `x` is the center plus coefficients of absolute value at most one times the radius
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exists_coeff_of_mem (I : Interval (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ I.construct) : -- --- CONCL ---
    ∃ β : Fin n → ℝ, (∀ i, |β i| ≤ 1) ∧
      ∀ i, x i = I.center i + β i * I.radius i := by -- --- PROOF ---
  -- each coordinate is within the radius of the center
  have h : ∀ i, |x i - I.center i| ≤ I.radius i := fun i => Interval.abs_sub_center_le hx i
  refine ⟨fun i => if I.radius i = 0 then 0 else (x i - I.center i) / I.radius i, ?_, ?_⟩
  · intro i
    by_cases h0 : I.radius i = 0
    · simp [h0]
    · have hpos : 0 < I.radius i := lt_of_le_of_ne (le_trans (abs_nonneg _) (h i)) (Ne.symm h0)
      simp only [if_neg h0]
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact h i
  · intro i
    by_cases h0 : I.radius i = 0
    · have := h i
      rw [h0] at this
      have : x i - I.center i = 0 := abs_nonpos_iff.mp this
      simp [h0]
      linarith
    · simp only [if_neg h0]
      field_simp
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
