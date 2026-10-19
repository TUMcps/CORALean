module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Eliminate
public import CORALean.Global.DropIdx
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ConPolyZono.reduceCon`

[1, Prop. 13]: constraint `r` is solved for the monomial of its constraint
generator `t`, and that monomial is substituted everywhere it occurs — in
generator `d`, which eq. (33) asks to carry the very same exponent column, and
in the constraint rows that stay, the latter being the constraint's own
`PolyLevelSet.eliminate`. One constraint and one constraint generator are gone, the generators
grow by one per surviving constraint generator.

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
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The surviving generator exponent columns, then the surviving constraint
exponent columns. -/
def ConPolyZono.aux_reduceConE {p h q : ℕ} (E : Fin p → Fin h → ℕ) (R : Fin p → Fin q → ℕ)
    (d : Fin h) (t : Fin q) : Fin p → Fin ((h - 1) + (q - 1)) → ℕ :=
  fun k => Fin.addCases (fun i => E k (dropIdx d i)) (fun i => R k (dropIdx t i))

/-- The generators that survive, then `G d` once per surviving constraint
generator, scaled by what the eliminated row gives it. -/
noncomputable def ConPolyZono.aux_reduceConG {α : Type} [AddCommGroup α] [Module ℝ α]
    {h m q : ℕ} (G : Fin h → α) (A : Mat ℝ m q) (r : Fin m) (d : Fin h) (t : Fin q) :
    Fin ((h - 1) + (q - 1)) → α :=
  Fin.addCases (fun i => G (dropIdx d i)) (fun i => (-(A r (dropIdx t i)) / A r t) • G d)


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
  G := ConPolyZono.aux_reduceConG cPZ.G cPZ.cons.A r d t
  E := ConPolyZono.aux_reduceConE cPZ.E cPZ.cons.R d t
  GI := cPZ.GI
  cons := cPZ.cons.eliminate r t
  cons_eq _ := cPZ.cons_eq _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
