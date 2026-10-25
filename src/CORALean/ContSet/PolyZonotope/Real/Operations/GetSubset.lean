module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetE
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetG

@[expose] public section

/-!
# `PolyZonotope.getSubset`

CORA's `@polyZonotope/getSubset`: one factor re-parametrized onto a sub-interval `cen ± rad` of
`[-1,1]`, so that the unit box of the new factors reaches what that sub-interval of the old one
reached ([1, Thm. 1]'s subject); this is the representation, `getSubsetG` at `getSubsetE`. An
exact change of variables, not an enclosure: the binomial expansion is a polynomial identity.
Center, factor count and independent block are untouched. CORA substitutes a list of factors at
once and prunes; here one factor is substituted (iterating gives the list), the uniform padding
keeps the generator index a product type, and pruning is `compact`'s job.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `cen` – subinterval center
* `rad` – subinterval radius

## Output
* polynomial zonotope for the factor restricted to the subinterval

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Factor `k` re-parametrized onto `cen ± rad`: every dependent generator
binomially expanded into `maxExp k + 1` of them. -/
def PolyZonotope.getSubset (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ) :
    PolyZonotope α where
  p := pZ.p
  h := pZ.h * (pZ.maxExp k + 1)
  q := pZ.q
  c := pZ.c
  G := pZ.getSubsetG k cen rad
  E := pZ.getSubsetE k
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
