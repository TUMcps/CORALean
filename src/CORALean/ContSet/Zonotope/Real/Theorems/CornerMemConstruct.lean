module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A sign corner lies in its zonotope

`c + ∑ ±gⱼ` is the point of coefficients `±1`, so it is a point of `construct`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.corner_mem_construct (Z : Zonotope α) (σ : Fin Z.h → Bool) :
    Z.corner σ ∈ Z.construct := by
  refine ⟨fun j => if σ j then 1 else -1, fun j => ?_, rfl⟩
  show |(if σ j = true then (1 : ℝ) else -1)| ≤ 1
  split_ifs <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
