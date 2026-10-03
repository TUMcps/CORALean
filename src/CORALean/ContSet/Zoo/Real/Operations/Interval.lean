import CORALean.ContSet.Zoo.Real.Zoo
import CORALean.ContSet.Interval.Real.Operations.Intersection
import CORALean.ContSet.Conversion.Real.Taylm_to_Interval

/-!
# `Zoo.interval`

CORA's `interval` of a zoo (`aux_zoo2int`): the intersection of the interval enclosures of the
members, from `(-∞, ∞)`. A zoo with no member is that unbounded interval, which `ℝ` bounds
cannot hold: `none`. The Taylor model's enclosure is its `'int'` range bound (`Taylm.interval`);
CORA's `taylm(bnb)`, `taylm(bnbAdv)`, `taylm(linQuad)` members, which differ only in the range
bound, are not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.interval (Z : Zoo n) : Option (Interval (Vec ℝ 1)) :=
  Option.merge Interval.intersection (Z.taylm.map fun T => Taylm.interval fun _ : Fin 1 => T) Z.ivl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
