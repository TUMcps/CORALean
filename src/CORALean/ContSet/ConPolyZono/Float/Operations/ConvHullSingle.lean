module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullG
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Copies
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Linear
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.Global.Float.IntRound
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
dropped (`Real.ConPolyZono.monomial_convHullE_padE`). The constraint is built as over ℝ, from
`PolyLevelSet.copies`, `PolyLevelSet.linear` and `PolyLevelSet.cartProd`; the weight row's
`1 - a` is stored from below by `intDown`, its slack the gap to `intUp`, so it only ever widens.

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

def ConPolyZono.convHullSingle (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) where
  p := a * cPZ.p + a
  h := a + (a * cPZ.h + a * cPZ.h)
  qI := 0
  c := fun i => nsmulDown a (cPZ.c i)
  G := ConPolyZono.convHullG a cPZ.c cPZ.G
  E := Real.ConPolyZono.convHullE a cPZ.E
  GI := Fin.elim0
  -- the copies' rows, each with its slack, and the weight row with its rounding gap
  cons := (cPZ.cons.copies a).cartProd (PolyLevelSet.linear (m := 1) (fun _ _ => one)
    (fun _ => intDown (1 - (a : ℤ))) (fun _ => subUp (intUp (1 - (a : ℤ))) (intDown (1 - (a : ℤ))))
    (fun _ => .eq) (Interval.unit a))
  cons_eq := Real.LevelSet.append_op_eq (fun _ => cPZ.cons_eq _) fun _ => rfl
  cons_dom := by
    show (cPZ.cons.dom.repVec a).append _ = _
    rw [cPZ.cons_dom]
    exact Interval.unit_append_unit _ _
  -- the operand's box, and what storing `a c` from below leaves to pay
  I_error := cPZ.I_error.plus (Interval.residual (fun i => nsmulDown a (cPZ.c i))
    (fun i => nsmulUp a (cPZ.c i)) (fun i => nsmulDown a (cPZ.c i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
