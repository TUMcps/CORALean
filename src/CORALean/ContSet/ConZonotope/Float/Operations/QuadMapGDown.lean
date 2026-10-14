module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
public import CORALean.ContSet.ConZonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.quadMapGDown`

The generators of [1, Lemma 1] on the stored centre and generators, rounded down: the linear
block `cᵀQ gⱼ + gⱼᵀQ c`, the squares `½ gⱼᵀQ gⱼ` (halving is exact) and one generator per pair
`j < k`, `gⱼᵀQ gₖ + gₖᵀQ gⱼ`, zero elsewhere. The blocks are the exact layer's, in its order.

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

/-- The generators of the enclosing zonotope, each rounded down. -/
def ConZonotope.quadMapGDown (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Fin m → Fin (cZ.h + cZ.h + cZ.h * cZ.h) → 𝕋 :=
  fun i => Fin.append
    (Fin.append
      (fun j => addDown (ConZonotope.quadBilDown (Q i) cZ.c (cZ.G j))
        (ConZonotope.quadBilDown (Q i) (cZ.G j) cZ.c))
      (fun j => half (ConZonotope.quadBilDown (Q i) (cZ.G j) (cZ.G j))))
    (fun l =>
      if (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
      then addDown
        (ConZonotope.quadBilDown (Q i) (cZ.G (finProdFinEquiv.symm l).1)
          (cZ.G (finProdFinEquiv.symm l).2))
        (ConZonotope.quadBilDown (Q i) (cZ.G (finProdFinEquiv.symm l).2)
          (cZ.G (finProdFinEquiv.symm l).1))
      else zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
