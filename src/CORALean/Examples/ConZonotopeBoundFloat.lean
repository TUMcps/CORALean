import CORALean.ContSet.ConZonotope.Float.Theorems.IsDisjointLPSound
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# A support value of a constrained zonotope, from the float LP driver

At `Dyadic 53`, values printed exactly through `ToRat`. Constrained zonotopes on the unit square's
generators: `ConZonotope.boundDot` reaches the support value where the constraint-blind zonotope
bound does not. Under `β₁ + β₂ = 0` the set is the segment `{(t, -t)}`, whose support in the
diagonal direction is `0`, where the zonotope bound is `2`; under `β₁ + β₂ ≤ 0` it is a triangle.
Under `3β₁ + β₂ ≤ 1` the support value in direction `(1, 0)` is `2/3`, not a dyadic, and the float
bound lands a few units in the last place above it, never below. `ConZonotope.boundDot_le` makes
each value a guarantee rather than a number.

## Inputs
* `cZ` – constrained zonotope
* `a` – direction

## Output
* support value as an exact rational
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ConZonotopeBoundFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- The unit square's generators, centered at the origin, no rounding error yet. -/
def square (P : HPolytope D (Vec D 2)) : ConZonotope D (Vec D 2) where
  h := 2
  c := ![d 0 0, d 0 0]
  G := ![![d 1 0, d 0 0], ![d 0 0, d 1 0]]
  P := P
  I_error := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- `β₁ + β₂ = 0`, an equality row:
the segment `{(t, -t)}`. -/
def eqRow : HPolytope D (Vec D 2) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, 1, fun _ _ => d 1 0, fun _ => d 0 0, fun _ => d 0 0,
    fun _ => d 0 0, Interval.origin _⟩

/-- `β₁ + β₂ ≤ 0`, an inequality row: a triangle. -/
def ineqRow : HPolytope D (Vec D 2) :=
  ⟨1, fun _ _ => d 1 0, fun _ => d 0 0, 0, fun i => i.elim0, fun i => i.elim0, fun _ => d 0 0,
    fun _ => d 0 0, Interval.origin _⟩

/-- `3β₁ + β₂ ≤ 1`, whose support value in direction `(1, 0)` is `2/3`, not a dyadic. -/
def thirdRow : HPolytope D (Vec D 2) :=
  ⟨1, fun _ j => if j = 0 then d 3 0 else d 1 0, fun _ => d 1 0, 0, fun i => i.elim0,
    fun i => i.elim0, fun _ => d 0 0, fun _ => d 0 0, Interval.origin _⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound in direction `a`, read exactly. -/
def bound (cZ : ConZonotope D (Vec D 2)) (a : Vec D 2) : ℚ :=
  ToRat.toRat (cZ.boundDot (c := rowLin (fun (_ : Fin 1) => a) 0) a fun _ => rfl).val

#eval bound (square eqRow) ![d 1 0, d 1 0]    -- 0, where the zonotope bound is 2
#eval bound (square eqRow) ![d 1 0, d 0 0]    -- 1
#eval bound (square ineqRow) ![d 1 0, d 1 0]  -- 0
#eval bound (square ineqRow) ![d (-1) 0, d 0 0]  -- 1
#eval bound (square thirdRow) ![d 1 0, d 0 0] - 2 / 3  -- a few ulps above 2/3, never below

end CORALean.Examples.ConZonotopeBoundFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
