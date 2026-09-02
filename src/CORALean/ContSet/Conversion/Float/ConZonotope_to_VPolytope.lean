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

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConZonotope.vPolytopeBox (C : ConZonotope 𝕋 n) : VPolytope 𝕋 n :=
  Interval.vPolytope C.interval

theorem ConZonotope.subset_vPolytopeBox (C : ConZonotope 𝕋 n) :
    C.construct ⊆ C.vPolytopeBox.construct :=
  subset_trans C.interval_outer (Interval.subset_vPolytope _)

end CORALean.Float
