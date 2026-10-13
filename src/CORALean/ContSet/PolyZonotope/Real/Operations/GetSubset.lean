module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetE
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetG

@[expose] public section

/-!
# `PolyZonotope.getSubset`

CORA's `@polyZonotope/getSubset`: one factor re-parametrized onto a sub-interval
`cen ± rad` of `[-1,1]`, so that the unit box of the new factors reaches what
that sub-interval of the old one reached. What such a sub-box names is [1, Thm. 1]'s
subject; this is the representation of it, `getSubsetG` at `getSubsetE`.

An exact change of variables and not an enclosure, above degree one as much as
at it: the binomial expansion is a polynomial identity. Centre, factor count and
independent block are untouched, so a caller's sub-box needs no transport.

CORA substitutes a list of factors at once, expands each column only as far as
its own degree, folds the constant columns into the centre, merges the duplicate
ones and drops the factors nothing reads. Here one factor is substituted —
iterating gives the list — and the uniform padding is what keeps the generator
index a product type; the pruning is `compact`'s job in this tree.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
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
