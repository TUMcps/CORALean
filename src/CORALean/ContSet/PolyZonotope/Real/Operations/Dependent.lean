import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `PolyZonotope.dependent`

The construction is [1, Prop. 1].

Every independent generator made dependent, by giving it a fresh factor that
appears in it alone and to the first power. Exact, and cheaply so: a factor
occurring in one generator only is as free as the coefficient it replaces.

CORA's `restructure` is this conversion paired with a reduction of the
independent block, so this is the exact half of it. It is also what `quadMap`
needs, being stated on a set whose coefficients are all dependent, which is what
lets `quadMap` be total without pretending about the cross terms an independent
block would contribute.

The exponent matrix is `plusE` against the identity, which is exactly right: the
fresh factors must not reach the original generators, and the original factors
must not reach the freed ones.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.dependent (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p + pZ.q
  h := pZ.h + pZ.q
  q := 0
  c := pZ.c
  G := Fin.append pZ.G pZ.GI
  E := PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q)
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
