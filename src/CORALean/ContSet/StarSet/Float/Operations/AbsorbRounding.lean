module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet

@[expose] public section

/-!
# `StarSet.absorbRounding`

The error box made part of the star set: `n` further factors, each ranging over the box's own
interval `[inf, sup]` in its coordinate, and added to the point by identity generators. A factor
box is exactly what a star set already has, so nothing is widened: the old rows read the old
factors only (a zero for each new one), every stored entry is a stored float, `zero` or `one`,
so nothing rounds, and the box left over is the origin.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
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
  cons := s.cons.map fun r => (Fin.append r.1 fun _ => zero, r.2)
  l := Fin.append s.l s.I_error.inf
  u := Fin.append s.u s.I_error.sup
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
