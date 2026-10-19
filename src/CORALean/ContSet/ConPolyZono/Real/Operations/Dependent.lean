module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
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

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.dependent (cPZ : ConPolyZono α) : ConPolyZono α where
  p := cPZ.p + cPZ.qI
  h := cPZ.h + cPZ.qI
  qI := 0
  c := cPZ.c
  G := Fin.append cPZ.G cPZ.GI
  E := PolyZonotope.plusE cPZ.E (PolyZonotope.identE cPZ.qI)
  GI := Fin.elim0
  cons := cPZ.cons.padVars cPZ.qI
  cons_eq := cPZ.cons_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
