import CORALean.NN.Layers.Operations.TapMat
import CORALean.NN.Layers.Theorems.TapEntryDot
import Mathlib.Data.Matrix.Mul

/-!
# A stencil matrix times a vector

Row `j` of the product is the weighted sum over output `j`'s taps, the weights read into ℝ:
`tapEntry_dot` at that row, which is why the taps of every row must be injective.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


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
