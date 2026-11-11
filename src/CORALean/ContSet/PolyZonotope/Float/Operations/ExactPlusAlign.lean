module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Float.Operations.PadBack

@[expose] public section

/-!
# `exactPlus` of sets with different numbers of factors

CORA's `exactPlus` merges the exponent matrices by identifier. Here the factors are positions, and
a set that has fewer is padded with factors it does not depend on, at the back; the sum shares the
factors of the first `min` positions, which is where an operation that only appends factors (as
`absorbRounding` does) leaves a set's own.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Output
* the sum keeping the dependency on the shared factors
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `exactPlus` after padding the set with fewer factors. -/
def PolyZonotope.exactPlusAlign (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  if h : pZ₁.p ≤ pZ₂.p then
    (pZ₁.padBack (pZ₂.p - pZ₁.p)).exactPlus pZ₂ (by simp only [PolyZonotope.padBack]; omega)
  else
    pZ₁.exactPlus (pZ₂.padBack (pZ₁.p - pZ₂.p)) (by simp only [PolyZonotope.padBack]; omega)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
