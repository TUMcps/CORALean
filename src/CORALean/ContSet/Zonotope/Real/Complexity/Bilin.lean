import CORALean.ContSet.Zonotope.Real.Operations.Bilin

/-!
# `Zonotope.bilin_h`

`bilin`'s generator count: each operand's own, plus the cross block at their
product — quadratic, not linear, in the operands' sizes. `rfl`, since
`Operations/Bilin.lean` states `h` directly. `BilinBigO.lean` puts this in
`O`-notation, along a family of operands whose sizes grow.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bilin_h (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z₁ : Zonotope α) (Z₂ : Zonotope β) :
    (Zonotope.bilin f Z₁ Z₂).h = Z₁.h + Z₂.h + Z₁.h * Z₂.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
