module

public import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE
public import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG

@[expose] public section

/-!
# `PolyZonotope.bilin`

Any bilinear map applied to two polynomial zonotopes over the *same* factors. The result is
again a polynomial zonotope, exactly, because `f` distributes over the two sums and the product
of two monomials is the monomial at the added exponent column. Sharing is a hypothesis rather
than a shape in the signature (`p` is a field): `Fin.cast` reads `pZ₂`'s exponent matrix at
`pZ₁`'s factor indices, which moves no data. The independent blocks take no part, so `bilin`
is a claim about `point`; a caller who needs those coefficients to count runs `dependent`
first, and once, so that repeated pairings keep the freed ones identified.

## Inputs
* `f` – bilinear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope of the bilinear image
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.bilin (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope γ where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.bilinG f pZ₁ pZ₂
  E := PolyZonotope.bilinE pZ₁ pZ₂ hp
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
