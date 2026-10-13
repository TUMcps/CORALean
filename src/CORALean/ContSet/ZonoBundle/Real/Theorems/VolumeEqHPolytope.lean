module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ExistsHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Volume

@[expose] public section

/-!
# The volume of a bundle is that of its polytope

CORA takes `volume(polytope(zB))`: the bundle's polytope has the bundle's volume
(`exists_hPolytope`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.volume_eq_hPolytope (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ∃ P : HPolytope (Vec ℝ n), P.volume = zB.volume := by
  obtain ⟨P, hP⟩ := zB.exists_hPolytope hk
  exact ⟨P, by unfold HPolytope.volume ZonoBundle.volume; rw [hP]⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
