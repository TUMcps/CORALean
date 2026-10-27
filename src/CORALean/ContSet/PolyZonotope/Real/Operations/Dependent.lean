module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

@[expose] public section

/-!
# `PolyZonotope.dependent`

The construction is [1, Prop. 1]. Every independent generator made dependent, by giving it a
fresh factor that appears in it alone and to the first power. Exact, and cheaply so: a factor
occurring in one generator only is as free as the coefficient it replaces. CORA's
`restructure` is this paired with a reduction of the independent block. It is what `quadMap`
needs, being stated on a set whose coefficients are all dependent. The exponent matrix is
`plusE` against the identity: the fresh factors must not reach the original generators, nor
the original factors the freed ones.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with independent generators turned into factors

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


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
