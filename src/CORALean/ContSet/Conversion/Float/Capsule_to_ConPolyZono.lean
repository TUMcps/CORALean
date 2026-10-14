module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_ConPolyZono

@[expose] public section

/-!
# A capsule as a constrained polynomial zonotope, over a floating-point scalar

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion, as over ℝ: the capsule is first replaced by its axis-aligned box,
which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.conPolyZono_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.conPolyZono.construct :=
  subset_trans C.interval_contains (Interval.conPolyZono_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
