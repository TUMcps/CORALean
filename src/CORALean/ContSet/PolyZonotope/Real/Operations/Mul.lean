import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `PolyZonotope.mul`

The coordinatewise product of two polynomial zonotopes over the *same* factors,
and what raises a polynomial abstraction above order two [1]: `quadMap` gives
order two — the elementwise square is its case `Q k = eₖ eₖᵀ` — and every order
above it is this operation applied again. Generator `(i, j)` is the plain
product `G¹ᵢ ⊙ G²ⱼ` at the exponent column `E¹ᵢ + E²ⱼ`, a monomial again, which
is what the shared factors buy.

Sharing is a hypothesis rather than a shape in the signature: `p` is a field, so
two `PolyZonotope`s cannot be made to share it definitionally without
destructuring one of them. `Fin.cast` then reads `S₂`'s exponent matrix at
`S₁`'s factor indices, which moves no data — identity here is positional.

The independent blocks take no part, a product of two free coefficients not
being one, so `mul` is a claim about `point`; a caller who needs those
coefficients to count runs `dependent` first, and once, so that repeated
products keep the freed ones identified.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Generator `(i, j)` of the product: the two extended generators, multiplied
coordinate by coordinate. -/
def PolyZonotope.mulG (S₁ S₂ : PolyZonotope (Vec ℝ n)) :
    Fin ((S₁.h + 1) * (S₂.h + 1)) → Vec ℝ n :=
  fun l i => PolyZonotope.extG S₁ (finProdFinEquiv.symm l).1 i
      * PolyZonotope.extG S₂ (finProdFinEquiv.symm l).2 i

/-- Its exponent column, the two columns added, `S₂`'s read at `S₁`'s factor
indices. -/
def PolyZonotope.mulE (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    Fin S₁.p → Fin ((S₁.h + 1) * (S₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

def PolyZonotope.mul (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    PolyZonotope (Vec ℝ n) where
  p := S₁.p
  h := (S₁.h + 1) * (S₂.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.mulG S₁ S₂
  E := PolyZonotope.mulE S₁ S₂ hp
  GI := Fin.elim0

end CORALean.Real
