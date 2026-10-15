module

public import CORALean.ContSet.Ellipsoid.Float.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin

@[expose] public section

/-!
# `Ellipsoid.excludesPoint`, over a floating-point scalar

A certified `p ∉ E`, the other half of a membership decision `Ellipsoid.containsPoint` gives only
one half of. A direction `a` separates: if every point of the set reads at most the float bound
`boundDot` in direction `a` and the point reads strictly more, the point is outside. The direction
and the proposed length `s ≥ √(aᵀ Q a)` (the square root the bound needs) are the caller's; `s` is
checked by one float comparison, and the reading of the point is rounded down. Only `true` is
certain; `false` says only that this direction does not separate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.excludesPoint (E : Ellipsoid 𝕋 n) (p a : Vec 𝕋 n) (s : 𝕋) : Bool :=
  if hs : le (E.quadUp a) (mulDown s s) = true then
    -- the set's bound in direction `a`, strictly below the point's reading
    let bound := E.boundDot (c := rowLin (fun (_ : Fin 1) => a) 0) a (fun _ => rfl) s
      (toReal_le_of_le hs)
    ltStrict bound.val (dotDown a p)
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
