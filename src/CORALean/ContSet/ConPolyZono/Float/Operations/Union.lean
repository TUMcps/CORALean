module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpper
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLower
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
public import CORALean.ContSet.PolyLevelSet.Float.Operations.And
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff

@[expose] public section

/-!
# `ConPolyZono.union`

CORA's `@conPolyZono/or`, [1, Thm. 1], as the exact layer lays it out: the center at the midpoint,
one generator `(c₁ - c₂) / 2` whose factor is the branch selector, then both operands' generators,
and the selector constraints over two fresh factors.

The midpoint and the sliding generator are rounded down, their shortfalls paid into the box; the
selector polynomial is stored scaled to integer coefficients (`unionConInt`), what that cost being
its row's slack (`unionConErr`). No independent generators, as over ℝ. That the result holds both
operands rests on `Real.ConPolyZono.union_relax_subset`.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* enclosure of the union

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.union (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p + 2
  h := 1 + (cPZ₁.h + cPZ₂.h)
  qI := 0
  c := PolyZonotope.midpoint cPZ₁.c cPZ₂.c
  G := Fin.append (fun _ => PolyZonotope.halfDiff cPZ₁.c cPZ₂.c) (Fin.append cPZ₁.G cPZ₂.G)
  E := Real.ConPolyZono.unionE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  -- the selector rows, the second with its coefficients' rounding, then the operands' own rows
  cons := (ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).andRows
    (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons)
  cons_eq := Real.LevelSet.append_op_eq
    (Real.LevelSet.append_op_eq (fun _ => rfl) fun _ => rfl)
    (Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq)
  cons_dom := rfl
  -- the boxes of both operands, and what storing the center and the generator cost
  I_error := (cPZ₁.I_error.or cPZ₂.I_error).plus
    ((PolyZonotope.midpointResidual cPZ₁.c cPZ₂.c).plus
      (PolyZonotope.halfDiffError cPZ₁.c cPZ₂.c))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
