module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
public import CORALean.ContSet.ConZonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.quadMapCDown`

The center of [1, Lemma 1], `cᵀQ c + ½ Σⱼ gⱼᵀQ gⱼ`, rounded down; the sum is
accumulated downward and halved exactly.

## Inputs
* `Q` – quadratic form matrices
* `cZ` – float constrained zonotope

## Output
* center of the quadratic image rounded down

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

/-- The center of the enclosing zonotope, from below. -/
def ConZonotope.quadMapCDown (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Vec 𝕋 m :=
  fun i => addDown (ConZonotope.quadBilDown (Q i) cZ.c cZ.c)
    (half (sumDown fun s => ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
