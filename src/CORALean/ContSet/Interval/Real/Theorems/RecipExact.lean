module

public import CORALean.ContSet.Interval.Real.Operations.Recip
public import CORALean.ContSet.Interval.Real.Theorems.InvBetween
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# `Interval.recip` is exactly the reciprocal image

For a box that avoids `0` in every coordinate, the reciprocal is antitone on the side of `0` the
coordinate lies on, so the corners swap and nothing between them is missed. The two signs of a
coordinate are handled by one scalar lemma and its mirror, so a box may mix them.

## Inputs
* `J` – second interval box

## Hypotheses
* `hne` – `J` nonempty
* `hJ` – no coordinate of `J` contains zero

## Conclusion
* the reciprocal box is exactly the image of `J`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Conversely, a value between the reciprocals is the reciprocal of a point between. -/
theorem Interval.aux_inv_mem {a b z : ℝ} (hab : a ≤ b) (h : 0 < a ∨ b < 0) (h₁ : b⁻¹ ≤ z)
    (h₂ : z ≤ a⁻¹) : ∃ y, (a ≤ y ∧ y ≤ b) ∧ y⁻¹ = z := by -- --- PROOF ---
  rcases h with ha | hb
  · have hz : 0 < z := lt_of_lt_of_le (inv_pos.mpr (ha.trans_le hab)) h₁
    refine ⟨z⁻¹, ⟨?_, ?_⟩, inv_inv z⟩
    · simpa using inv_anti₀ hz h₂
    · simpa using inv_anti₀ (inv_pos.mpr (ha.trans_le hab)) h₁
  · have ha : a < 0 := lt_of_le_of_lt hab hb
    have hz : z < 0 := lt_of_le_of_lt h₂ (inv_lt_zero.mpr ha)
    refine ⟨z⁻¹, ⟨?_, ?_⟩, inv_inv z⟩
    · simpa using (inv_le_inv_of_neg (inv_lt_zero.mpr ha) hz).mpr h₂
    · simpa using (inv_le_inv_of_neg hz (inv_lt_zero.mpr hb)).mpr h₁


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.recip_exact (J : Interval (Vec ℝ n)) (hne : J.IsNonempty)
    (hJ : ∀ i, 0 < J.inf i ∨ J.sup i < 0) :
    J.recip.construct = (fun y i => (y i)⁻¹) '' J.construct := by -- --- PROOF ---
  ext z
  constructor
  · intro hz
    have h : ∀ i, ∃ y, (J.inf i ≤ y ∧ y ≤ J.sup i) ∧ y⁻¹ = z i := fun i =>
      Interval.aux_inv_mem (hne i) (hJ i) (hz i).1 (hz i).2
    choose y hy hyz using h
    exact ⟨y, fun i => hy i, funext hyz⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact Interval.inv_between (hJ i) (hy i).1 (hy i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
