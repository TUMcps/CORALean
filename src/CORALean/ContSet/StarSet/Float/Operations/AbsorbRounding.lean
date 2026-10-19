module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet
public import CORALean.ContSet.HPolytope.Float.Operations.Lift

@[expose] public section

/-!
# `StarSet.absorbRounding`

The error box made part of the star set: `n` further factors, each ranging over the box's own
interval `[inf, sup]` in its coordinate, and added to the point by identity generators. A factor
box is exactly what a star set already has, so nothing is widened: the coefficient box is
appended with the error box (`Interval.append`), the predicate is lifted to read the old factors
only (`HPolytope.lift_`, #174), every stored entry is a stored float, `zero` or `one`, so nothing
rounds, and the box left over is the origin.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The error box as `n` further factors over the box's own bounds, the box left over the origin. -/
def StarSet.absorbRounding (s : StarSet 𝕋 n) : StarSet 𝕋 n where
  m := s.m + n
  c := s.c
  G := fun i => Fin.append (s.G i) fun k => if k = i then one else zero
  -- `n` factors over the box's bounds, read by no row: the box appended
  dom := s.dom.append s.I_error
  -- the predicate lifted; its row slacks `b_error` and `be_error` stay, as `lift_` keeps them
  pred := s.pred.lift_ (Fin.castAdd n)
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
