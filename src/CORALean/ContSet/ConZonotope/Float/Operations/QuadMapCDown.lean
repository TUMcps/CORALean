import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp

/-!
# `ConZonotope.quadMapCDown`

The centre of [1, Lemma 1], `cᵀQ c + ½ Σⱼ gⱼᵀQ gⱼ`, rounded down; the sum is
accumulated downward and halved exactly.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre of the enclosing zonotope, from below. -/
def ConZonotope.quadMapCDown (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n) : Vec 𝕋 m :=
  fun i => addDown (ConZonotope.quadBilDown (Q i) cZ.c cZ.c)
    (half (sumDown fun s => ConZonotope.quadBilDown (Q i) (fun r => cZ.G r s) fun r => cZ.G r s))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
