module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ConPolyZono.dependent`

`PolyZonotope.dependent` with the constraints carried along: every independent
generator made dependent, by giving it a fresh factor that appears in it alone
and to the first power. Exact, and cheaply so — a factor occurring in one
generator only is as free as the coefficient it replaces.

Here it earns more than it does for a polynomial zonotope. The constraints reach
the dependent factors and nothing else, so an operation stated as a constraint —
`intersection` above all — is exact only on a set whose coefficients are all dependent.
`dependent` is what makes that a restriction on nothing: it is applied first,
and it loses nothing.

The fresh factors take exponent zero in every constraint row, which is what
`padE` says. They have to: the constraints were written against the original
factors, and a fresh factor appearing in one would silently change them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.dependent (cPZ : ConPolyZono α) : ConPolyZono α where
  p := cPZ.p + cPZ.q
  h := cPZ.h + cPZ.q
  q := 0
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := Fin.append cPZ.G cPZ.GI
  E := PolyZonotope.plusE cPZ.E (PolyZonotope.identE cPZ.q)
  GI := Fin.elim0
  A := cPZ.A
  b := cPZ.b
  EC := ConPolyZono.padE cPZ.EC cPZ.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
