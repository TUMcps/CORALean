import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConA
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConB
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConE
import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceConG

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

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Constraint `r` eliminated, by solving it for constraint generator `t`'s
monomial and substituting that into generator `d` and into the rows that stay. -/
noncomputable def ConPolyZono.reduceCon {α : Type} [AddCommGroup α] [Module ℝ α]
    (cPZ : ConPolyZono α) (r : Fin cPZ.m) (d : Fin cPZ.h) (t : Fin cPZ.s) : ConPolyZono α where
  p := cPZ.p
  h := (cPZ.h - 1) + (cPZ.s - 1)
  q := cPZ.q
  m := cPZ.m - 1
  s := cPZ.s - 1
  c := cPZ.c + (cPZ.b.inf r / cPZ.A r t) • cPZ.G d
  G := ConPolyZono.reduceConG cPZ.G cPZ.A r d t
  E := ConPolyZono.reduceConE cPZ.E cPZ.EC d t
  GI := cPZ.GI
  A := ConPolyZono.reduceConA cPZ.A r t
  b := ConPolyZono.reduceConB cPZ.A cPZ.b r t
  EC := fun k i => cPZ.EC k (dropIdx t i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
