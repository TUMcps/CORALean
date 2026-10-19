module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet
public import CORALean.ContSet.StarSet.Float.Operations.Basic

@[expose] public section

/-!
# `StarSet.absorbRounding`

The error box made part of the star set: `n` further factors, each ranging over the box's own
interval `[inf, sup]` in its coordinate, and added to the point by identity generators. A factor
box is exactly what a star set already has, so nothing is widened: the old rows read the old
factors only (a zero for each new one), every stored entry is a stored float, `zero` or `one`,
so nothing rounds, and the box left over is the origin. The new factors are the predicate's own
`StarSet.LinPred.append` (#174), whose membership is `StarSet.LinPred.mem_append_nominal_iff`.
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
  -- the predicate's own `append`: `n` factors over the box's bounds, read by no row
  pred := s.pred.append s.I_error.inf s.I_error.sup
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
