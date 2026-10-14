module

public import CORALean.ContSet.ZonoBundle.Real.Operations.IsCentre
public import CORALean.ContSet.HPolytope.Real.Theorems.IsLPCentreMem
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact

@[expose] public section

/-!
# The centre of a zonotope bundle lies in it

The centre is `c + G β` for a coefficient vector `β` feasible in the domain of `conZonotope(zB)`,
which denotes the bundle exactly (`conZonotopeAll_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.IsCentre.mem {zB : ZonoBundle (Vec ℝ n)} {hk : 0 < zB.k} {x : Vec ℝ n}
    (hx : zB.IsCentre hk x) : x ∈ zB.construct := by
  obtain ⟨β, hβ, rfl⟩ := hx
  rw [← ZonoBundle.conZonotopeAll_exact zB hk]
  obtain ⟨hb, hP⟩ := ConZonotope.mem_domain_iff.mp hβ.mem
  exact ⟨β, hb, hP, rfl⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
