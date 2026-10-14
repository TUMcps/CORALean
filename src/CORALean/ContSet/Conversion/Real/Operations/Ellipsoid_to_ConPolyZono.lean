module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope — the construction

`Ellipsoid.conPolyZonoR` and `Ellipsoid.conPolyZono` are the constructions;
`Ellipsoid_to_ConPolyZono` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The diagonal constraint exponent matrix: factor `j` reads its own square
everywhere except the last row, which reads the slack factor to the first
power alone. -/
def Ellipsoid.conPolyZonoR (k : ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun r c => if r = c then (if c.val < k then 2 else 1) else 0

/-- `E.k` dependent factors read `E.G`'s columns exactly as `E`'s own affine map
does; one further factor absorbs the unit ball's radius slack. -/
noncomputable def Ellipsoid.conPolyZono (E : Ellipsoid n) : ConPolyZono (Vec ℝ n) where
  p := E.k + 1
  h := E.k
  qI := 0
  m := 1
  q := E.k + 1
  c := E.c
  G := ConPolyZono.consCol E.G
  E := ConPolyZono.padE (PolyZonotope.identE E.k) 1
  GI := Fin.elim0
  A := fun _ j => if j.val < E.k then 1 else -(1 / 2)
  b := Interval.point fun _ => (1 / 2 : ℝ)
  R := Ellipsoid.conPolyZonoR E.k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
