import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope

/-!
# A bundle is a constrained zonotope

`representsa_(zB, 'conZonotope')` is `true`: with a first member, the folded intersection of the
members' constrained zonotopes (`conZonotopeAll`) denotes the bundle.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.exists_conZonotope (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ∃ cZ : ConZonotope (Vec ℝ n), cZ.construct = zB.construct :=
  ⟨zB.conZonotopeAll hk, ZonoBundle.conZonotopeAll_exact zB hk⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
