module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.Convex

@[expose] public section

/-!
# A float ellipsoid is convex

What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.convex_construct (E : Ellipsoid 𝕋 n) : Convex ℝ E.construct :=
  InflatedContSet.convex_construct E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
