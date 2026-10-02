import CORALean.ContSet.Capsule.Real.Operations.Plus
import CORALean.Global.EuclideanNorm

/-!
# The sum of two capsules, against the first one's generator

A point of the sum is `x₁ + x₂` with `xᵢ = cᵢ + tᵢ gᵢ + bᵢ`, `‖bᵢ‖₂ ≤ rᵢ`. Against `g₁` it is
`(c₁ + c₂) + t₁ g₁` plus `b₁ + b₂ + t₂ g₂`, whose length is under `r₁ + r₂ + ‖g₂‖₂`. The statement
holds whichever generator is the longer, which is what lets a float comparison of the lengths
choose either branch of `Capsule.plus`.
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
theorem Capsule.plus_outer_keep_left (C₁ C₂ : Capsule n) {x₁ x₂ : Vec ℝ n}
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
