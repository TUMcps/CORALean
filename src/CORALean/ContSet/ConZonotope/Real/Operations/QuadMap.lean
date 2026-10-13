import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
import CORALean.ContSet.HPolytope.Real.Operations.Comap

/-!
# `ConZonotope.quadMap`

CORA's `@conZonotope/quadMap` for a single constrained zonotope (`aux_quadMapSingle`) [2]: the
generators of `Zonotope.quadMap` [1, Lemma 1] on the centre and generators, with the constraint
`A β = b` kept on the *linear* block, the factors that are the old ones, and the new factors for
the squares `2βⱼ² - 1` and the products `βⱼβₖ` unconstrained. The new factors do not satisfy the
constraints on the old ones, which is what makes the result an outer approximation and no more.

CORA first runs `rescale 'iter'` when there are constraints, which narrows the coefficient box
before the squares are taken. That only tightens the result; it is not needed for the enclosure
and is not part of this operation. The mixed form `quadMap(cZ1, cZ2, Q)` is not modelled.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_quadMapSingle`: `Z.quadMap Q` with the constraints on the linear block. -/
noncomputable def ConZonotope.quadMap (Q : Fin m → Mat ℝ n n) (cZ : ConZonotope (Vec ℝ n)) :
    ConZonotope (Vec ℝ m) :=
  let Z : Zonotope (Vec ℝ n) := ⟨cZ.h, cZ.c, cZ.G⟩
  { h := (Z.quadMap Q).h
    c := (Z.quadMap Q).c
    G := (Z.quadMap Q).G
    P := cZ.P.comap ((blockLeft cZ.h cZ.h).comp (blockLeft (cZ.h + cZ.h) (cZ.h * cZ.h))) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
