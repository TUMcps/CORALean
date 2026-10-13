import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.ofEntryBoundsMat`

How every operation here rounds: it computes, entry by entry, floats either side of the
exact centre and of each exact generator, and this stores the lower ones. The centre's gap
is `matResidual`; a generator's gap, scaled by a coefficient in `[-1, 1]`, is at most its
width, so the widths summed upward bound the rest, as a symmetric box. Both join the box
`E` the operation already owes, and the generator count is the exact one's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower bounds stored, the gaps to the upper ones paid into the box beside `E`. -/
def Zonotope.ofEntryBoundsMat {h : ℕ} (cLo cHi : Mat 𝕋 m n) (GLo GHi : Fin h → Mat 𝕋 m n)
    (E : Interval (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 m n) :=
  let W : Mat 𝕋 m n := fun i j => sumUp fun k => subUp (GHi k i j) (GLo k i j)   -- Σ widths
  let Ec := Interval.matResidual cLo cHi cLo                                       -- centre gap
  { h := h
    c := cLo
    G := GLo
    E := Interval.matPlus (Interval.matPlus E Ec) ⟨fun i j => neg (W i j), W⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
