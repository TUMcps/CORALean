module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConA
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConB
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConE
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConG

@[expose] public section

/-!
# `ConPolyZono.reduceCon`

[1, Prop. 13]: constraint `r` is solved for the monomial of its constraint
generator `t`, and that monomial is substituted everywhere it occurs — in
generator `d`, which eq. (33) asks to carry the very same exponent column, and
in the constraint rows that stay. One constraint and one constraint generator
are gone, the generators grow by one per surviving constraint generator.

[1] follows this with `compactGens` and with restricting the exponent rows to
those that are not all zero. Neither is applied here: [1] says of both that they
only change the representation, and `compactGens` is its own operation.

Real only. The construction divides by `A(r,t)`, and a rounded quotient is not a
rounded *set* — the surviving rows would constrain something else — so a float
layer wants an interval-valued correction, which is a design and not a rounding
of this one.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Constraint `r` eliminated, by solving it for constraint generator `t`'s
monomial and substituting that into generator `d` and into the rows that stay. -/
noncomputable def ConPolyZono.reduceCon {α : Type} [AddCommGroup α] [Module ℝ α]
    (cPZ : ConPolyZono α) (r : Fin cPZ.cons.m) (d : Fin cPZ.h) (t : Fin cPZ.cons.q) :
    ConPolyZono α where
  p := cPZ.p
  h := (cPZ.h - 1) + (cPZ.cons.q - 1)
  qI := cPZ.qI
  c := cPZ.c + (cPZ.cons.b r / cPZ.cons.A r t) • cPZ.G d
  G := ConPolyZono.reduceConG cPZ.G cPZ.cons.A r d t
  E := ConPolyZono.reduceConE cPZ.E cPZ.cons.R d t
  GI := cPZ.GI
  cons :=
    { m := cPZ.cons.m - 1
      q := cPZ.cons.q - 1
      A := ConPolyZono.reduceConA cPZ.cons.A r t
      R := fun k i => cPZ.cons.R k (dropIdx t i)
      b := ConPolyZono.reduceConB cPZ.cons.A cPZ.cons.b r t
      op := fun _ => .eq }
  cons_eq _ := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
