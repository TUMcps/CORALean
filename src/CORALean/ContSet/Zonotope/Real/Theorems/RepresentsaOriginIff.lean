import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaPointIff

/-!
# `Zonotope.representsa_origin_iff`

The origin is the point whose centre is `0`: `{c} = {0}` iff `c = 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsa_origin_iff (Z : Zonotope α) :
    Z.construct = {0} ↔ Z.representsa_origin := by -- --- PROOF ---
  constructor
  · intro h
    have hc : Z.c = 0 := by
      have := Zonotope.centre_mem_construct Z
      rw [h] at this
      exact this
    refine ⟨hc, (Zonotope.representsa_point_iff Z).mp ?_⟩
    rw [h, hc]
  · rintro ⟨hc, hp⟩
    rw [← hc]
    exact (Zonotope.representsa_point_iff Z).mpr hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
