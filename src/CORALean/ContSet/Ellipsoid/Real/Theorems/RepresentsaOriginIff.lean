module

public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaPointIff

@[expose] public section

/-!
# `Ellipsoid.representsa_origin_iff`

The origin is the point whose centre is `0`: `{q} = {0}` iff `q = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.representsa_origin_iff (E : Ellipsoid n) :
    E.construct = {0} ↔ E.representsa_origin := by -- --- PROOF ---
  constructor
  · intro h
    have hc : E.q = 0 := by
      have := Ellipsoid.centre_mem_construct E
      rw [h] at this
      exact this
    refine ⟨hc, (Ellipsoid.representsa_point_iff E).mp ?_⟩
    rw [h, hc]
  · rintro ⟨hc, hp⟩
    rw [← hc]
    exact (Ellipsoid.representsa_point_iff E).mpr hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
