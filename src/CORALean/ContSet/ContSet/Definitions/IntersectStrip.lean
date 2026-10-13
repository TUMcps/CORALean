module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Meeting a set with strips

CORA's `intersectStrip`, [1, Prop. 6]: the set met with the strips
`|C x - y| ≤ φ`, weighted by a gain `Λ`. Outer for every gain, so the gain decides only how tight
the result is, never whether it is sound. The strips are given in the representation's own
scalar and read as reals through `Scalar`, so a float representation computes them in floats
and the guarantee is about the reals they store.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar


-- ========================================  MAIN TYPE  ========================================= --

/-- The set met with the strips of `C`, `φ`, `y` at the gain `Λ`, outer for every gain. -/
class IntersectStrip (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  intersectStrip {n p : ℕ} : Mat 𝕋 p n → Vec 𝕋 p → Vec 𝕋 p → Mat 𝕋 n p → S n → S n
  intersectStrip_outer {n p : ℕ} (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : Mat 𝕋 n p) (s : S n) :
    construct s ∩ {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (φ i)} ⊆
      construct (intersectStrip C φ y Λ s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
