module

public import CORALean.ContSet.PolyZonotope.Real.Operations.MulG

@[expose] public section

/-!
# A coordinate of a product generator

`mulG` is `bilinG` at the entrywise product, so a coordinate of it is a product
of two coordinates — true by `rfl`, but a proof that reads the generator
entrywise has to rewrite with it rather than unfold three definitions.

Its own file (#62) because the float layer's `Theorems/MulGClose.lean` is what
reads it, and that is where the rounding of a product generator is priced.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `l` – generator index
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* the entry is the product of the factors' entries
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mulG_apply (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n))
    (l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1))) (i : Fin n) : -- --- CONCL ---
    PolyZonotope.mulG pZ₁ pZ₂ l i
      = PolyZonotope.extG pZ₁ (finProdFinEquiv.symm l).1 i
        * PolyZonotope.extG pZ₂ (finProdFinEquiv.symm l).2 i := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
