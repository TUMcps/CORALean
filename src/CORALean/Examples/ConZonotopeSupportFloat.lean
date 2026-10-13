import CORALean.ContSet.ConZonotope.Float.Theorems.IsDisjointLPSound
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# The float LP driver, run

At `Dyadic 53`, values printed exactly through `ToRat`. Constrained zonotopes on
the unit square's generators: `ConZonotope.boundDot` reaches the support value
where the constraint-blind zonotope bound does not, and lands a few units in the
last place above a non-dyadic one, never below. A bundle whose members each reach
`x = 2` but meet only where `x ≤ 3/8`: the least member bound says `2`,
`ZonoBundle.boundDotLP` says `3/8`. Two parallel segments whose interval hulls
overlap: `ConZonotope.isDisjointLP` finds the separating direction.

`ConZonotope.boundDot_le`, `ZonoBundle.boundDotLP_le` and
`ConZonotope.isDisjointLP_sound` make each value a guarantee rather than a number.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ConZonotopeSupportFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- The unit square's generators, centred at the origin, no rounding error yet. -/
def square (P : HPolytope D (Vec D 2)) : ConZonotope D (Vec D 2) where
  h := 2
  c := ![d 0 0, d 0 0]
  G := ![![d 1 0, d 0 0], ![d 0 0, d 1 0]]
  P := P
  E := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- `β₁ + β₂ = 0`, an equality row with a point interval as its right-hand side:
the segment `{(t, -t)}`. -/
def eqRow : HPolytope D (Vec D 2) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, 1, fun _ _ => d 1 0,
    ⟨fun _ => d 0 0, fun _ => d 0 0⟩⟩

/-- `β₁ + β₂ ≤ 0`, an inequality row: a triangle. -/
def ineqRow : HPolytope D (Vec D 2) :=
  ⟨1, fun _ _ => d 1 0, fun _ => d 0 0, 0, fun i => i.elim0,
    ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- `3β₁ + β₂ ≤ 1`, whose support value in direction `(1, 0)` is `2/3`, not a dyadic. -/
def thirdRow : HPolytope D (Vec D 2) :=
  ⟨1, fun _ j => if j = 0 then d 3 0 else d 1 0, fun _ => d 1 0, 0, fun i => i.elim0,
    ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- The segment moved by `(1/2, 1/2)`: parallel to it, disjoint, the same hull. -/
def shifted : ConZonotope D (Vec D 2) := { square eqRow with c := ![d 1 (-1), d 1 (-1)] }

/-- A flat box `[-2, 2] × [-1/8, 1/8]` and a thin parallelogram along the
diagonal, no rounding error yet. -/
def bundle : ZonoBundle (Vec D 2) :=
  ⟨2, ![⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 0 0], ![d 0 0, d 1 (-3)]],
          ⟨fun _ => d 0 0, fun _ => d 0 0⟩⟩,
        ⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 2 0], ![d 1 (-3), d (-1) (-3)]],
          ⟨fun _ => d 0 0, fun _ => d 0 0⟩⟩]⟩

/-- Direction `(1, 0)`. -/
def e₁ : Vec D 2 := ![d 1 0, d 0 0]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound in direction `a`, read exactly. -/
def bound (cZ : ConZonotope D (Vec D 2)) (a : Vec D 2) : ℚ :=
  ToRat.toRat (cZ.boundDot (c := rowLin (fun (_ : Fin 1) => a) 0) a fun _ => rfl).val

#eval bound (square eqRow) ![d 1 0, d 1 0]    -- 0, where the zonotope bound is 2
#eval bound (square eqRow) ![d 1 0, d 0 0]    -- 1
#eval bound (square ineqRow) ![d 1 0, d 1 0]  -- 0
#eval bound (square ineqRow) ![d (-1) 0, d 0 0]  -- 1
#eval bound (square thirdRow) ![d 1 0, d 0 0] - 2 / 3  -- a few ulps above 2/3, never below

#eval (square eqRow).isDisjointLP shifted     -- true: parallel segments
#eval (square eqRow).isDisjointLP (square ineqRow)  -- false: they meet

-- 2, the least member bound
#eval ToRat.toRat (bundle.boundDot (by decide) (c := rowLin (fun (_ : Fin 1) => e₁) 0) e₁
  fun _ => rfl).val
-- 3/8, the linear program over the intersection
#eval ToRat.toRat (bundle.boundDotLP (by decide) (c := rowLin (fun (_ : Fin 1) => e₁) 0) e₁
  fun _ => rfl).val

end CORALean.Examples.ConZonotopeSupportFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
