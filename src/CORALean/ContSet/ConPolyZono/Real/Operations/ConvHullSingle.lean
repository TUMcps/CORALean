module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Copies
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Linear
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullG

@[expose] public section

/-!
# `ConPolyZono.convHullSingle`

CORA's `aux_convHullSingle`, the construction of [1, Prop. 9] applied to one
set: `a` copies of it, each over its own block of factors and its own copy of
the constraint system, weighted by `a` fresh factors whose sum one extra row
fixes. That is a convex combination of `a` of the set's points, and at
`a = dim + 1` Carathéodory says those are the whole convex hull.

The constraint is the operand's, copied onto each block (`PolyLevelSet.copies`), beside the
weight row, a linear level set (`PolyLevelSet.linear`) on the weight factors
(`PolyLevelSet.cartProd`).

No independent generators: a coefficient answering to no constraint would be
free in every copy at once, which is not what a weighted sum of points means.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a` weighted copies of one set, as one constrained polynomial zonotope. -/
noncomputable def ConPolyZono.convHullSingle {α : Type} [AddCommGroup α] [Module ℝ α] (a : ℕ)
    (cPZ : ConPolyZono α) : ConPolyZono α where
  p := a * cPZ.p + a
  h := a + (a * cPZ.h + a * cPZ.h)
  qI := 0
  c := (a : ℝ) • cPZ.c
  G := ConPolyZono.convHullG a cPZ.c cPZ.G
  E := ConPolyZono.convHullE a cPZ.E
  GI := Fin.elim0
  -- the copies' rows, then the weight row `∑ⱼ λⱼ = 1 - a`
  cons := (cPZ.cons.copies a).cartProd
    (PolyLevelSet.linear (m := 1) (fun _ _ => 1) (fun _ => 1 - (a : ℝ)) (fun _ => .eq)
      (Interval.unit a))
  cons_eq := LevelSet.append_op_eq (fun _ => cPZ.cons_eq _) fun _ => rfl
  cons_dom := by
    show (cPZ.cons.dom.repVec a).append _ = _
    rw [cPZ.cons_dom]
    exact Interval.unit_append_unit _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
