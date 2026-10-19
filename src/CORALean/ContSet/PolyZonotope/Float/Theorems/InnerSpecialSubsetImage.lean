module

public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerSpecial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerTestSubsetImage

@[expose] public section

/-!
# `innerSpecial` proves an inner box

`innerSpecial` is `innerTest` with `ind` the identity, so `innerTest_subset_image` is its
guarantee: `true` puts `Y` inside the image of `X` under the dependent point map, which is
what [1, Alg. 2] claims of `Inner`: `Inner(f, x, x̃, ỹ) = 1 ⟹ ỹ ⊆ range(f, x)`.

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerSpecial_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n))
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) (h : n = pZ.p)
    (hT : PolyZonotope.innerSpecial pZ X X₀ Y inv iter h = true) : -- --- CONCL ---
    Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct :=
  PolyZonotope.innerTest_subset_image pZ X X₀ Y _ _ _ iter hT

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
