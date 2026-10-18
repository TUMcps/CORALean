module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullA
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullB
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullG
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullR
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.convHullSingle`

CORA's `aux_convHullSingle`, [1, Prop. 9] applied to one set: `a` copies of it, each over
its own block of factors and its own copy of the constraint system, weighted by `a` fresh factors
whose sum one extra row fixes. The center `a c` is the only thing that rounds, stored from below
with its shortfall in the box; the box of the operand is kept, a convex combination of points of a
box being in it.

No independent generators, as over ℝ. Each copy keeps its operand's slack; the exact hull of the
operand's nominal set, whose slack factors sit inside each copy, reads as this layout with them
dropped (`Real.ConPolyZono.monomial_convHullE_padE`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.convHullSingle (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) where
  p := a * cPZ.p + a
  h := a + (a * cPZ.h + a * cPZ.h)
  qI := 0
  m := a * cPZ.m + 1
  q := a * cPZ.q + a
  c := fun i => nsmulDown a (cPZ.c i)
  G := ConPolyZono.convHullG a cPZ.c cPZ.G
  E := Real.ConPolyZono.convHullE a cPZ.E
  GI := Fin.elim0
  A := ConPolyZono.convHullA a cPZ.A
  b := ConPolyZono.convHullB a cPZ.b
  -- each copy's slack, and the weight row's rounding gap
  b_error := Fin.append (Real.ConPolyZono.repVec a cPZ.b_error)
    (fun _ => subUp (intUp (1 - (a : ℤ))) (intDown (1 - (a : ℤ))))
  R := Real.ConPolyZono.convHullR a cPZ.R
  -- the operand's box, and what storing `a c` from below leaves to pay
  I_error := cPZ.I_error.plus (Interval.residual (fun i => nsmulDown a (cPZ.c i))
    (fun i => nsmulUp a (cPZ.c i)) (fun i => nsmulDown a (cPZ.c i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
