import CORALean.ContSet.PolyZonotope.Real.Operations.MulG

/-!
# A coordinate of a product generator

`mulG` is `bilinG` at the entrywise product, so a coordinate of it is a product
of two coordinates — true by `rfl`, but a proof that reads the generator
entrywise has to rewrite with it rather than unfold three definitions.

Its own file (#62) because the float layer's `Theorems/MulGClose.lean` is what
reads it, and that is where the rounding of a product generator is priced.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mulG_apply (S₁ S₂ : PolyZonotope (Vec ℝ n))
    (l : Fin ((S₁.h + 1) * (S₂.h + 1))) (i : Fin n) :
    PolyZonotope.mulG S₁ S₂ l i
      = PolyZonotope.extG S₁ (finProdFinEquiv.symm l).1 i
        * PolyZonotope.extG S₂ (finProdFinEquiv.symm l).2 i := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
