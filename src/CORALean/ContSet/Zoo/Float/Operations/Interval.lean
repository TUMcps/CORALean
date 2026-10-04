import CORALean.ContSet.Zoo.Float.Zoo
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Interval.Float.Operations.Intersection

/-!
# `Zoo.interval`, over a floating-point scalar

The intersection of the members' interval enclosures: the Taylor model's range bound `bounds`
(`Taylm.interval` at one component) meets the stored interval; a missing member leaves the other.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.interval (Z : Zoo 𝕋 n) : Option (Interval (Vec 𝕋 1)) :=
  Option.merge Interval.intersection
    (Z.taylm.map fun T => ⟨fun _ => T.bounds.1, fun _ => T.bounds.2⟩) Z.ivl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
