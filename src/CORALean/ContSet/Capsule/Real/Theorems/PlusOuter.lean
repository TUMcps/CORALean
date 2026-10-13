module

public import CORALean.ContSet.Capsule.Real.Operations.Plus
public import CORALean.ContSet.Capsule.Real.Theorems.PlusOuterKeepLeft
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Capsule.plus` encloses the sum

A point of the sum is `x₁ + x₂` with `xᵢ = cᵢ + tᵢ gᵢ + bᵢ`, `‖bᵢ‖₂ ≤ rᵢ`. Against the longer
generator, say `g₁`, it is `(c₁ + c₂) + t₁ g₁` plus `b₁ + b₂ + t₂ g₂`, whose length is under
`r₁ + r₂ + ‖g₂‖₂`. Outer only: the sum of two capsules is not a capsule, and the enclosure is
strict in general.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum of two capsules lies in `Capsule.plus`. -/
theorem Capsule.plus_outer (C₁ C₂ : Capsule n) :
    C₁.construct + C₂.construct ⊆ (C₁.plus C₂).construct := by -- --- PROOF ---
  rintro _ ⟨x₁, h₁, x₂, h₂, rfl⟩
  unfold Capsule.plus
  split_ifs
  · exact Capsule.plus_outer_keep_left C₁ C₂ h₁ h₂
  · have := Capsule.plus_outer_keep_left C₂ C₁ h₂ h₁
    rwa [add_comm x₂ x₁, add_comm C₂.c C₁.c, add_comm C₂.r C₁.r] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
