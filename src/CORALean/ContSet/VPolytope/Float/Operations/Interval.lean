import CORALean.ContSet.VPolytope.Float.Operations.SupportBound

/-!
# `VPolytope.interval`, over a floating-point scalar

The box around the vertices, widened by the error box. Both bounds come from
`SupportBound`, so nothing is computed here — the file exists to give CORA's
`interval(polytope)` a name at this layer.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.interval (P : VPolytope 𝕋 n) : Interval 𝕋 n :=
  Interval.ofBounds P.boundProj P.boundNegProj

end CORALean.Float
