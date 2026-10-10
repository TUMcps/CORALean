import CORALean.ContSet.PolyZonotope.Float.Operations.InnerSpecial
import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerTestSubsetImage

/-!
# `innerSpecial` proves an inner box

`innerSpecial` is `innerTest` with `ind` the identity, so `innerTest_subset_image` is its
guarantee: `true` puts `Y` inside the image of `X` under the dependent point map.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerSpecial_subset_image (pZ : PolyZonotope 𝕋 n)
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n))
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) (h : n = pZ.p)
    (hT : PolyZonotope.innerSpecial pZ X X₀ Y inv iter h = true) :
    Y.construct ⊆ (GPolyZonotope.nominal pZ).point '' X.construct :=
  PolyZonotope.innerTest_subset_image pZ X X₀ Y _ _ _ iter hT

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
