import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
import CORALean.ContSet.ZonoBundle.Real.Theorems.ExistsHPolytope
import CORALean.ContSet.HPolytope.Real.Operations.Volume

/-!
# The volume of a bundle is that of its polytope

CORA takes `volume(polytope(zB))`: the bundle's polytope has the bundle's volume
(`exists_hPolytope`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
