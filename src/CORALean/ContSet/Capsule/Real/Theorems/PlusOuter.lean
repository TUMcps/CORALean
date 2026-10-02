import CORALean.ContSet.Capsule.Real.Operations.Plus
import CORALean.Global.EuclideanNorm

/-!
# `Capsule.plus` encloses the sum

A point of the sum is `x₁ + x₂` with `xᵢ = cᵢ + tᵢ gᵢ + bᵢ`, `‖bᵢ‖₂ ≤ rᵢ`. Against the longer
generator, say `g₁`, it is `(c₁ + c₂) + t₁ g₁` plus `b₁ + b₂ + t₂ g₂`, whose length is under
`r₁ + r₂ + ‖g₂‖₂`. Outer only: the sum of two capsules is not a capsule, and the enclosure is
strict in general.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum, against the generator of `C₁`, when it is the longer one. -/
private theorem plus_outer_aux (C₁ C₂ : Capsule n) {x₁ x₂ : Vec ℝ n}
    (h₁ : x₁ ∈ C₁.construct) (h₂ : x₂ ∈ C₂.construct) :
    x₁ + x₂ ∈ (Capsule.mk (C₁.c + C₂.c) C₁.g
      (C₁.r + C₂.r + Real.sqrt (∑ i, C₂.g i ^ 2))).construct := by -- --- PROOF ---
  obtain ⟨t₁, ht₁, hb₁⟩ := h₁
  obtain ⟨t₂, ht₂, hb₂⟩ := h₂
  refine ⟨t₁, ht₁, ?_⟩
  have hb₁' : ‖x₁ - (C₁.c + t₁ • C₁.g)‖₂ ≤ C₁.r := hb₁
  have hb₂' : ‖x₂ - (C₂.c + t₂ • C₂.g)‖₂ ≤ C₂.r := hb₂
  have hg : ‖t₂ • C₂.g‖₂ ≤ ‖C₂.g‖₂ := by
    rw [norm₂_smul]
    exact mul_le_of_le_one_left (norm₂_nonneg _) (abs_le.mpr ht₂)
  have hsplit : x₁ + x₂ - (C₁.c + C₂.c + t₁ • C₁.g) =
      (x₁ - (C₁.c + t₁ • C₁.g)) + (x₂ - (C₂.c + t₂ • C₂.g)) + t₂ • C₂.g := by abel
  change ‖x₁ + x₂ - (C₁.c + C₂.c + t₁ • C₁.g)‖₂ ≤ _
  rw [hsplit]
  calc _ ≤ ‖(x₁ - (C₁.c + t₁ • C₁.g)) + (x₂ - (C₂.c + t₂ • C₂.g))‖₂ + ‖t₂ • C₂.g‖₂ :=
        norm₂_add_le _ _
    _ ≤ (‖x₁ - (C₁.c + t₁ • C₁.g)‖₂ + ‖x₂ - (C₂.c + t₂ • C₂.g)‖₂) + ‖C₂.g‖₂ :=
        add_le_add (norm₂_add_le _ _) hg
    _ ≤ _ := add_le_add (add_le_add hb₁' hb₂') le_rfl

/-- The sum of two capsules lies in `Capsule.plus`. -/
theorem Capsule.plus_outer (C₁ C₂ : Capsule n) :
    C₁.construct + C₂.construct ⊆ (C₁.plus C₂).construct := by -- --- PROOF ---
  rintro _ ⟨x₁, h₁, x₂, h₂, rfl⟩
  unfold Capsule.plus
  split_ifs
  · exact plus_outer_aux C₁ C₂ h₁ h₂
  · have := plus_outer_aux C₂ C₁ h₂ h₁
    rwa [add_comm x₂ x₁, add_comm C₂.c C₁.c, add_comm C₂.r C₁.r] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
