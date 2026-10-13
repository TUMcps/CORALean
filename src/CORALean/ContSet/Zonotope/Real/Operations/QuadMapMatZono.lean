import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul

/-!
# `Zonotope.quadMapMatZono`

[1, Thm. 1]: the quadratic map `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z}` with each `Q⁽ⁱ⁾` ranging over a
matrix zonotope `(D⁽ⁱ⁾, K⁽ⁱ'¹⁾, ..., K⁽ⁱ'ᵛ⁾)`, enclosed by
`Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ ([-1, 1] ⊗ Z_K(ν))`, each partial zonotope [1, Lemma 1]'s at
the centres `D⁽ⁱ⁾` or at the `j`-th generators `K⁽ⁱ'ʲ⁾`, the interval product [1, Eq. 11]'s,
and the sum [1, Eq. 10]'s: centres added, generators concatenated. `K j i` is `K⁽ⁱ'ʲ⁾`.

The `ν` interval products have the origin as centre, so the sum's centre is `Z_D`'s, and
their generators are read off `Fin ν × Fin (p + p + p² + 1)` through `finProdFinEquiv`.

What the enclosure needs, `quadMapMatZono_outer` says: one factor `βⱼ` per generator `j`,
shared by all `i`, as the printed proof has it; for factors chosen per `i`, as the printed
set has it, `quadMapMatZono_not_outer` is a counterexample.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m ν : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1]: `Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ ([-1, 1] ⊗ Z_K(ν))`. -/
noncomputable def Zonotope.quadMapMatZono (D : Fin m → Mat ℝ n n) (K : Fin ν → Fin m → Mat ℝ n n)
    (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ m) :=
  let ZD := Z.quadMap D                                  -- `Z_D`, Lemma 1 at the centres
  let ZK := fun j => (Z.quadMap (K j)).unitIntervalMul   -- `[-1, 1] ⊗ Z_K(j)`, Lemma 1 and (11)
  { h := ZD.h + ν * (Z.h + Z.h + Z.h * Z.h + 1)            -- the sum, as in (10)
    c := ZD.c
    G := Fin.append ZD.G fun l => (ZK (finProdFinEquiv.symm l).1).G (finProdFinEquiv.symm l).2 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
