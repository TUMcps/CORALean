module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaPointIff

@[expose] public section

/-!
# `Zonotope.representsa_origin_iff`

The origin is the point whose center is `0`: `{c} = {0}` iff `c = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsa_origin_iff (Z : Zonotope α) :
    Z.construct = {0} ↔ Z.representsa_origin := by -- --- PROOF ---
  constructor
  · intro h
    have hc : Z.c = 0 := by
      have := Zonotope.center_mem_construct Z
      rw [h] at this
      exact this
    refine ⟨hc, (Zonotope.representsa_point_iff Z).mp ?_⟩
    rw [h, hc]
  · rintro ⟨hc, hp⟩
    rw [← hc]
    exact (Zonotope.representsa_point_iff Z).mpr hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
