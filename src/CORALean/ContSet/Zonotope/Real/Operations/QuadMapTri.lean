module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapPairIdx
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.quadMapTri`

[1, Lemma 1 (generators)] with its generators as printed: the center
`dᵢ = cᵀQ⁽ⁱ⁾c + 0.5 Σₛ g⁽ˢ⁾ᵀQ⁽ⁱ⁾g⁽ˢ⁾`, the `p` linear generators `h⁽ʲ⁾ᵢ = cᵀQ⁽ⁱ⁾g⁽ʲ⁾ + g⁽ʲ⁾ᵀQ⁽ⁱ⁾c`,
the `p` squares `h⁽ᵖ⁺ʲ⁾ᵢ = 0.5 g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾`, and one generator
`h⁽²ᵖ⁺ˡ⁾ᵢ = g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ᵏ⁾ + g⁽ᵏ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾` for each pair `j < k` alone, numbered by
`quadMapPairIdx`. That is `σ = C(p + 2, 2) - 1` generators. `Zonotope.quadMap` indexes the pair
block by all of `Fin p × Fin p`, zero off `j < k`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 1 (generators)]: the enclosing zonotope, the pair block over `j < k` only. -/
noncomputable def Zonotope.quadMapTri (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h + Z.h + Z.h.choose 2
  c := fun i => Z.c ⬝ᵥ (Q i *ᵥ Z.c) + (1 / 2) * ∑ s, Z.G s ⬝ᵥ (Q i *ᵥ Z.G s)
  G := Fin.append
    (Fin.append
      (fun j i => Z.c ⬝ᵥ (Q i *ᵥ Z.G j) + Z.G j ⬝ᵥ (Q i *ᵥ Z.c))
      (fun j i => (1 / 2) * Z.G j ⬝ᵥ (Q i *ᵥ Z.G j)))
    (fun l i =>
      let jk := (Zonotope.quadMapPairIdx Z.h l).1
      Z.G jk.1 ⬝ᵥ (Q i *ᵥ Z.G jk.2) + Z.G jk.2 ⬝ᵥ (Q i *ᵥ Z.G jk.1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
