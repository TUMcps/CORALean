module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyLevelSet.Real.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `ConPolyZono.getSubset`

CORA's `@conPolyZono/getSubset`, and [1, Prop. 14] (`subset`) at one factor:
`PolyZonotope.getSubset` applied to the generator block (`toPolyZonotope`) and the constraint's
own `PolyLevelSet.getSubset`, which applies it to the rows' polynomial part — the same split
CORA's own implementation makes. `b` takes no part in either and so is carried across unchanged.

The binomial expansion itself is not reproved here: it is
`PolyZonotope.getSubset_point`'s, read at the generators in `Theorems/GetSubsetConstruct.lean`
and at the rows in `PolyLevelSet.eval_getSubset`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Factor `r` re-parametrized onto `cen ± rad`: every generator and every
constraint column binomially expanded into as many new ones as its degree in
`r` takes. -/
def ConPolyZono.getSubset (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ) :
    ConPolyZono α where
  p := cPZ.p
  h := (cPZ.toPolyZonotope.getSubset r cen rad).h
  qI := cPZ.qI
  c := cPZ.c
  G := (cPZ.toPolyZonotope.getSubset r cen rad).G
  E := (cPZ.toPolyZonotope.getSubset r cen rad).E
  GI := cPZ.GI
  cons := cPZ.cons.getSubset r cen rad
  cons_eq := cPZ.cons_eq
  cons_dom := cPZ.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
