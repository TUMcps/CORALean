module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.quadMap`

[1, Lemma 1]: the quadratic map `Z_Q = {λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z}` of a zonotope
`Z = (c, g⁽¹⁾, ..., g⁽ᵖ⁾)`, enclosed by the zonotope `(d, h⁽¹⁾, ..., h⁽σ⁾)` with
`dᵢ = cᵀQ⁽ⁱ⁾c + 0.5 Σₛ g⁽ˢ⁾ᵀQ⁽ⁱ⁾g⁽ˢ⁾`, the linear generators `h⁽ʲ⁾ᵢ = cᵀQ⁽ⁱ⁾g⁽ʲ⁾ + g⁽ʲ⁾ᵀQ⁽ⁱ⁾c`,
the squares `h⁽ᵖ⁺ʲ⁾ᵢ = 0.5 g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾` and one generator per pair `j < k`,
`g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ᵏ⁾ + g⁽ᵏ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾` — CORA's `@zonotope/quadMap` for a single zonotope.

The pair block is indexed by all of `Fin p × Fin p`, zero off `j < k`, as in
`Zonotope.quadTaylor`: `p + p + p²` generators where the lemma counts
`σ = C(p + 2, 2) - 1`, the extra ones zero and so the same set. `m` outputs rather than
the lemma's `n`, nothing depending on the two agreeing.

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

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 1]: the zonotope enclosing `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z}`. -/
noncomputable def Zonotope.quadMap (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h + Z.h + Z.h * Z.h
  c := fun i => Z.c ⬝ᵥ (Q i *ᵥ Z.c) + (1 / 2) * ∑ s, Z.G s ⬝ᵥ (Q i *ᵥ Z.G s)
  G := Fin.append
    (Fin.append
      (fun j i => Z.c ⬝ᵥ (Q i *ᵥ Z.G j) + Z.G j ⬝ᵥ (Q i *ᵥ Z.c))
      (fun j i => (1 / 2) * Z.G j ⬝ᵥ (Q i *ᵥ Z.G j)))
    (fun l i =>
      let jk := finProdFinEquiv.symm l
      if jk.1 < jk.2 then Z.G jk.1 ⬝ᵥ (Q i *ᵥ Z.G jk.2) + Z.G jk.2 ⬝ᵥ (Q i *ᵥ Z.G jk.1)
      else 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
