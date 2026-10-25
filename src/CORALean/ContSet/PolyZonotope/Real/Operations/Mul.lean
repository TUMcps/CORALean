module

public import CORALean.ContSet.PolyZonotope.Real.Operations.MulE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MulG

@[expose] public section

/-!
# `PolyZonotope.mul`

The coordinatewise product of two polynomial zonotopes over the *same* factors, at one
dimension [1, Prop. 2.9], and what raises a polynomial abstraction above order two: `quadMap`
gives order two and every order above it is this operation applied again, [1, Prop. 2.10].
Generator `(i, j)` is `mulG`, at the exponent column `mulE`, a monomial again. Sharing is a
hypothesis rather than a shape in the signature (`p` is a field): `Fin.cast` reads `pZ₂`'s
exponent matrix at `pZ₁`'s factor indices. The independent blocks take no part, so `mul` is a
claim about `point`; a caller who needs those coefficients to count runs `dependent` first,
and once, so that repeated products keep the freed ones identified.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope of the entrywise product

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
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
