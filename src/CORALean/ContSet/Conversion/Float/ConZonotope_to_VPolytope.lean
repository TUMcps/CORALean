import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope

/-!
# A constrained zonotope as vertices, over a floating-point scalar

Through its box, and named `vPolytopeBox` for it — the exact layer's
`ConZonotope.vPolytope` enumerates the coefficient domain's vertices, and that
route asks which rows of the domain are tight, which is an equality test on
reals.

Deciding it in floating point means solving each square subsystem with directed
rounding and keeping an enclosure of the solution, which is verified interval
linear algebra and an algorithm in its own right rather than a rounding of this
one. Until that exists, the box is what a definition can give, exactly as for
`HPolytope.vPolytopeBox` at this layer.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConZonotope.vPolytopeBox (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope cZ.interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.vPolytopeBox_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.vPolytopeBox.construct :=
  subset_trans cZ.interval_contains (Interval.vPolytope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
