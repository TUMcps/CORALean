module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# `PolyZonotope.quadMapMixed`

CORA's `@polyZonotope/quadMap` at two operands, and the `mu(D, R₁, R₂)` a conservative
polynomialization is written in: `{(x₁ᵀQ₁x₂, …) | x₁ ∈ pZ₁, x₂ ∈ pZ₂}`, the arguments ranging
*independently*. `quadMapDep` pairs a set with itself over shared factors; here nothing may be
shared, or the ranges would be tied together. Independence is what `cartProd` buys (`[1, Prop.
11]`'s block-diagonal layout); `bilin` then pairs that product with itself at the map reading
the *first* component of one argument against the *second* of the other. `[1, Prop. 12]` is the
same pairing where the operands are one set. `dependent` runs on each operand first.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Output
* polynomial zonotope of the mixed quadratic image

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic map of two sets whose arguments range independently, CORA's
`quadMap(pZ₁, pZ₂, Q)`. -/
def PolyZonotope.quadMapMixed (Q : Fin m → Mat ℝ n n) (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) :=
  PolyZonotope.bilin
    ((PolyZonotope.quadBilin Q).compl₁₂
      (LinearMap.fst ℝ (Vec ℝ n) (Vec ℝ n)) (LinearMap.snd ℝ (Vec ℝ n) (Vec ℝ n)))
    (pZ₁.dependent.cartProd pZ₂.dependent) (pZ₁.dependent.cartProd pZ₂.dependent) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
