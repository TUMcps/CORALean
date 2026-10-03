import CORALean.ContSet.Capsule.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaPointIff

/-!
# A capsule is the origin iff it is a point at `0`

The point is the centre, so the origin is the point whose centre is `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.representsa_origin_iff (hn : 0 < n) (C : Capsule n) :
    C.construct = {0} ↔ C.representsa_origin := by -- --- PROOF ---
  constructor
  · intro h
    have hc : C.c ∈ C.construct :=
      (Capsule.centre_mem_construct_iff C).mpr (by
        obtain ⟨t, -, ht⟩ : (0 : Vec ℝ n) ∈ C.construct := h ▸ rfl
        exact le_trans (Real.sqrt_nonneg _) ht)
    rw [h] at hc
    refine ⟨hc, (Capsule.representsa_point_iff hn C).mp ?_⟩
    rw [h, hc]
  · rintro ⟨hc, hp⟩
    rw [← hc]
    exact (Capsule.representsa_point_iff hn C).mpr hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
