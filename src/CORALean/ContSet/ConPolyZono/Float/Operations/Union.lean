module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperA
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpperB
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperEC
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerEC
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff

@[expose] public section

/-!
# `ConPolyZono.union`

CORA's `@conPolyZono/or`, [1, Thm. 1], as the exact layer lays it out: the centre
at the midpoint, one generator `(c₁ - c₂) / 2` whose factor is the branch selector, then both
operands' generators unchanged, and the selector constraints over two fresh factors.

The midpoint and the sliding generator are rounded down and their shortfalls paid into
the box, as `linComb`'s are; the box also holds both operands' boxes (`Interval.or`),
which each branch carries along. The operands' constraint blocks are copied, and the
selector polynomial is stored scaled to integer coefficients (`unionConInt`).

No independent generators: as over ℝ, there is nothing for them to mean here.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.union (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p + 2
  h := 1 + (cPZ₁.h + cPZ₂.h)
  q := 0
  m := 1 + 1 + (cPZ₁.m + cPZ₂.m)
  s := 1 + (2 + (cPZ₁.p + cPZ₁.p + (cPZ₂.p + cPZ₂.p + (cPZ₁.p * cPZ₂.p + cPZ₁.p * cPZ₂.p))))
    + (cPZ₁.s + cPZ₂.s + 1)
  c := PolyZonotope.midpoint cPZ₁.c cPZ₂.c
  G := Fin.append (fun _ => PolyZonotope.halfDiff cPZ₁.c cPZ₂.c) (Fin.append cPZ₁.G cPZ₂.G)
  E := Real.ConPolyZono.unionE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  A := ConPolyZono.plusA (ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
    (ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b)
  b := ConPolyZono.plusB (ConPolyZono.unionUpperB cPZ₁.p cPZ₂.p)
    (ConPolyZono.unionLowerB cPZ₁.b cPZ₂.b)
  EC := Real.ConPolyZono.appendE (Real.ConPolyZono.unionUpperEC cPZ₁.p cPZ₂.p)
    (Real.ConPolyZono.unionLowerEC cPZ₁.EC cPZ₂.EC)
  -- the boxes of both operands, and what storing the centre and the generator cost
  I_error := (cPZ₁.I_error.or cPZ₂.I_error).plus
    ((PolyZonotope.midpointResidual cPZ₁.c cPZ₂.c).plus
      (PolyZonotope.halfDiffError cPZ₁.c cPZ₂.c))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
