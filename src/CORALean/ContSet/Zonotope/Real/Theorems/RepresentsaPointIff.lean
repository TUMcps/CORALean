import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import Mathlib.Algebra.Module.BigOperators

/-!
# A zonotope is a point iff every generator vanishes

If `c + Gⱼ` (the coefficient `βⱼ = 1`, the others `0`) lies in `{c}` then `Gⱼ = 0`; conversely
with no generator the combination is `0`. The origin is the point whose centre is `0`. The empty
set is never represented: `Zonotope.centre_mem_construct` puts the centre in every zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsa_point_iff (Z : Zonotope α) :
    Z.construct = {Z.c} ↔ Z.representsa_point := by -- --- PROOF ---
  constructor
  · intro h j
    have hmem : Z.c + Z.G j ∈ Z.construct :=
      ⟨Pi.single j 1, fun i => by
        by_cases hij : i = j <;> simp [hij], by simp⟩
    rw [h] at hmem
    exact add_eq_left.mp hmem
  · intro h
    ext x
    constructor
    · rintro ⟨β, -, rfl⟩
      simp [h _]
    · rintro rfl
      exact Zonotope.centre_mem_construct Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
