module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleConstructSubsetSegmentAddBall
public import CORALean.ContSet.Conversion.Float.Theorems.EllipsoidConPolyZonoContains

@[expose] public section

/-!
# A capsule lies in its constrained polynomial zonotope, over a floating-point scalar

The capsule lies in its segment plus its ball (`Capsule.construct_subset_segment_add_ball`), each
conversion encloses its part, and the sum encloses theirs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.conPolyZono_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.conPolyZono.construct :=
  subset_trans C.construct_subset_segment_add_ball (subset_trans
    (Set.add_subset_add (Zonotope.conPolyZono_contains _) (Ellipsoid.conPolyZono_contains _))
    (ConPolyZono.plus_outer _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
