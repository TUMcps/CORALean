import CORALean.ContSet.ConZonotope.Float.Theorems.IsDisjointLPSound
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# Certifying two constrained zonotopes disjoint by a linear program

At `Dyadic 53`. Two parallel segments `{(t, -t)}` and `{(t + 1/2, 1/2 - t)}` have the same
interval hull, so a box test cannot separate them; `ConZonotope.isDisjointLP` finds the
separating direction. The segment and a triangle on the same generators do meet, and the
answer is `false`.

`ConZonotope.isDisjointLP_sound` makes each `true` a guarantee; a `false` decides nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ConZonotopeDisjointFloat

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The segment moved by `(1/2, 1/2)`: parallel to it, disjoint, the same hull. -/
def shifted : ConZonotope D (Vec D 2) := { square eqRow with c := ![d 1 (-1), d 1 (-1)] }

#eval (square eqRow).isDisjointLP shifted     -- true: parallel segments
#eval (square eqRow).isDisjointLP (square ineqRow)  -- false: they meet

end CORALean.Examples.ConZonotopeDisjointFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
