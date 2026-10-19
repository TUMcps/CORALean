module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.Basic

@[expose] public section

/-!
# A float zonotope lies in its facet polytope

Both branches are `Zonotope.hPolytope` at some rows, which holds the zonotope for any rows
(`Zonotope.hPolytope_contains`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float zonotope lies in CORA's `polytope(Z)` rows computed in floats. -/
theorem Zonotope.hPolytopeFacets_contains (p : ℕ) (Z : Zonotope (Vec 𝕋 (m + 1))) :
    Z.construct ⊆ (Z.hPolytopeFacets p).construct := by -- --- PROOF ---
  unfold Zonotope.hPolytopeFacets
  dsimp only
  split
  · exact Z.hPolytope_contains _
  · exact Z.hPolytope_contains _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
