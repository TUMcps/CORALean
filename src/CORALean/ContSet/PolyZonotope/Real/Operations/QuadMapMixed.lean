import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
import Mathlib.LinearAlgebra.Prod

/-!
# `PolyZonotope.quadMapMixed`

CORA's `@polyZonotope/quadMap` at two operands, and the `mu(D, R₁, R₂)` a
conservative polynomialization is written in: `{(x₁ᵀQ₁x₂, …) | x₁ ∈ pZ₁, x₂ ∈ pZ₂}`,
the two arguments ranging *independently*. `quadMapDep` pairs a set with itself
over shared factors; here nothing may be shared, or the two ranges would be tied
together and the result would shrink below the set asked for.

Independence is what `cartProd` buys — `[1, Prop. 11]`'s block-diagonal layout,
in which a factor vector of the product names a point of each operand with no
constraint between them. `bilin` then pairs that product with itself over those
factors, at the map reading the *first* component of one argument against the
*second* of the other; on the diagonal that is exactly `x₁ᵀQx₂`, with `x₁` and
`x₂` free of one another. `[1, Prop. 12]` is the same pairing where the two
operands are one set.

`dependent` runs on each operand first, for the reason `quadMap` runs it:
`bilin` is a claim about `point`, which an independent block takes no part in.

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
