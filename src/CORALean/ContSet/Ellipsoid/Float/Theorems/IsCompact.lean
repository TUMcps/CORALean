module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

@[expose] public section

/-!
# A float ellipsoid is compact

What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isCompact_construct (E : Ellipsoid 𝕋 n) : IsCompact E.construct :=
  InflatedContSet.isCompact_construct E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
