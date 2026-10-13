import CORALean.ContSet.PolyZonotope.Real.Operations.MulE
import CORALean.ContSet.PolyZonotope.Real.Operations.MulG

/-!
# `PolyZonotope.mul`

The coordinatewise product of two polynomial zonotopes over the *same* factors,
which at one dimension is [1, Prop. 2.9], and what raises a polynomial
abstraction above order two: `quadMap` gives order two — the elementwise square
is its case `Q k = eₖ eₖᵀ` — and every order above it is this operation applied
again, [1, Prop. 2.10]. Generator `(i, j)` is `mulG`, at the exponent column
`mulE`, a monomial again, which is what the shared factors buy.

Sharing is a hypothesis rather than a shape in the signature: `p` is a field, so
two `PolyZonotope`s cannot be made to share it definitionally without
destructuring one of them. `Fin.cast` then reads `pZ₂`'s exponent matrix at
`pZ₁`'s factor indices, which moves no data — identity here is positional.

The independent blocks take no part, a product of two free coefficients not
being one, so `mul` is a claim about `point`; a caller who needs those
coefficients to count runs `dependent` first, and once, so that repeated
products keep the freed ones identified.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mul (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope (Vec ℝ n) where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.mulG pZ₁ pZ₂
  E := PolyZonotope.mulE pZ₁ pZ₂ hp
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
