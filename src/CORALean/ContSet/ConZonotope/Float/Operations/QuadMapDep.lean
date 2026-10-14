module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDiff
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCDown
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCUp
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.quadMapDep`

`quadMap` at a set whose box is empty, on its factors: the enclosing zonotope of
[1, Lemma 1], whose first block of coefficients is the point's own and so meets the
constraints, and whose squares `2βⱼ² - 1` and products `βⱼβₖ` are free. The constraints are
therefore the operand's, padded by the two new blocks. The box holds what storing the centre and the
generators from below leaves to pay. Sound only where the operand's own box is empty, so nothing
outside `quadMap` calls it.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.quadMapDep (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    ConZonotope 𝕋 (Vec 𝕋 m) where
  h := cZ.h + cZ.h + cZ.h * cZ.h
  c := ConZonotope.quadMapCDown Q cZ
  G := fun l i => ConZonotope.quadMapGDown Q cZ i l
  P := (cZ.P.padLeft cZ.h).padLeft (cZ.h * cZ.h)
  E := (Interval.residual (ConZonotope.quadMapCDown Q cZ) (ConZonotope.quadMapCUp Q cZ)
    (ConZonotope.quadMapCDown Q cZ)).plus
      (Zonotope.generatorError (ConZonotope.quadMapGDiff Q cZ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
