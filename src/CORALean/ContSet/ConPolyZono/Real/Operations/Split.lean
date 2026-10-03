import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ConPolyZono
import CORALean.ContSet.Interval.Real.Operations.SplitAt

/-!
# `ConPolyZono.split`

CORA's `@conPolyZono/split` along one dimension `d`: take the box `I` around the set, cut it at
the middle of its `d`-th side into `I₁ = [inf, mid]` and `I₂ = [mid, sup]` there, and intersect
the set with each, `and_(cPZ, I, 'exact')`, which converts the box to a constrained polynomial
zonotope. A pair, as CORA returns both halves at once.

CORA's call without a dimension is this at every `d`, returned as a cell of pairs; that is the
map `d ↦ split cPZ d` and is not a separate definition.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The part of `cPZ` below and the part above the middle of its box along dimension `d`. -/
noncomputable def ConPolyZono.split (cPZ : ConPolyZono (Vec ℝ n)) (d : Fin n) :
    ConPolyZono (Vec ℝ n) × ConPolyZono (Vec ℝ n) :=
  let I := cPZ.interval
  -- the box cut at the middle of side `d`, `[inf, mid]` and `[mid, sup]` there
  let (I₁, I₂) := I.splitAt d
  (cPZ.intersection I₁.conPolyZono, cPZ.intersection I₂.conPolyZono)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
