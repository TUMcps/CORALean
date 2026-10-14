module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# `Interval.maxCos`

CORA's `aux_maxcos` in `@interval/cos`: the largest value of the cosine on `[lb, ub]`. The range
is shifted by a multiple `2πk` of the period so that its lower end lands in `(-2π, 0]`; then
either the shifted upper end reaches `0`, a maximum of the cosine, and the value is `1` (CORA's
`sign(b)`, which is `1` there or `0` at `b = 0`, where `cos b = 1`), or the shifted range lies in
`(-2π, 0)`, where the cosine falls and then rises, so the maximum is at an end.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.maxCos (lb ub : ℝ) : ℝ :=
  let k := ⌈lb / (2 * Real.pi)⌉
  let a := lb - 2 * Real.pi * k
  let b := ub - 2 * Real.pi * k
  let M := max (Real.cos a) (Real.cos b)
  max (Real.sign b) M

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
