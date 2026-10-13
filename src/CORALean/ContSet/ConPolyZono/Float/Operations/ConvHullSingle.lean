import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullA
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullB
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullG
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullEC
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual

/-!
# `ConPolyZono.convHullSingle`

CORA's `aux_convHullSingle`, [1, Prop. 9] applied to one set: `a` copies of it, each over
its own block of factors and its own copy of the constraint system, weighted by `a` fresh factors
whose sum one extra row fixes. The centre `a c` is the only thing that rounds, stored from below
with its shortfall in the box; the box of the operand is kept, a convex combination of points of a
box being in it.

No independent generators, as over ℝ.

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

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.convHullSingle (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) where
  p := a * cPZ.p + a
  h := a + (a * cPZ.h + a * cPZ.h)
  q := 0
  m := a * cPZ.m + 1
  s := a * cPZ.s + a
  c := fun i => nsmulDown a (cPZ.c i)
  G := ConPolyZono.convHullG a cPZ.c cPZ.G
  E := Real.ConPolyZono.convHullE a cPZ.E
  GI := Fin.elim0
  A := ConPolyZono.convHullA a cPZ.A
  b := ConPolyZono.convHullB a cPZ.b
  EC := Real.ConPolyZono.convHullEC a cPZ.EC
  -- the operand's box, and what storing `a c` from below leaves to pay
  err := cPZ.err.plus (Interval.residual (fun i => nsmulDown a (cPZ.c i))
    (fun i => nsmulUp a (cPZ.c i)) (fun i => nsmulDown a (cPZ.c i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
