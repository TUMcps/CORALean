import CORALean.NN.Layers.Operations.TapMat
import CORALean.NN.Layers.Theorems.TapEntryDot
import Mathlib.Data.Matrix.Mul

/-!
# A stencil matrix times a vector

Row `j` of the product is the weighted sum over output `j`'s taps, the weights read into ℝ:
`tapEntry_dot` at that row, which is why the taps of every row must be injective. At a
convolution's stencil this is [1, Sec. II (Conv to CAT)]: Appendix A's `W^F`, whose entries are
`Σ W_{i'j'k'} [l = idx(i', j', k')]`, times `x` is the convolution, at any injective stencil.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem tapMat_mulVec (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋)
    (htap : ∀ j, Function.Injective (tap j)) (x : Vec ℝ n) (j : Fin m) :
    (toRealMat (tapMat tap w) *ᵥ x) j = ∑ l, toReal (w j l) * x (tap j l) := by
  show ∑ i, toReal (tapEntry (tap j) (w j) i) * x i = _
  exact tapEntry_dot (tap j) (w j) x (htap j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
