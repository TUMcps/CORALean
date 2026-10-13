module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConsPolyZonotope
public import CORALean.ContSet.ConPolyZono.Real.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `ConPolyZono.getSubset`

CORA's `@conPolyZono/getSubset`, and [1, Prop. 14] (`subset`) at one factor:
`PolyZonotope.getSubset` applied to the generator block (`toPolyZonotope`) and,
separately, to the constraint block read as a `PolyZonotope` over `Vec ℝ m`
(`consPolyZonotope`) — the same split CORA's own implementation makes. `b`
takes no part in either call and so is carried across unchanged.

The binomial expansion itself is not reproved here: it is
`PolyZonotope.getSubset_point`'s, read once at the generators and once at the
constraint columns, in `Theorems/GetSubsetConstruct.lean`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
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
  q := cPZ.q
  m := cPZ.m
  s := (cPZ.consPolyZonotope.getSubset r cen rad).h
  c := cPZ.c
  G := (cPZ.toPolyZonotope.getSubset r cen rad).G
  E := (cPZ.toPolyZonotope.getSubset r cen rad).E
  GI := cPZ.GI
  A := fun i j => (cPZ.consPolyZonotope.getSubset r cen rad).G j i
  b := cPZ.b
  EC := (cPZ.consPolyZonotope.getSubset r cen rad).E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
