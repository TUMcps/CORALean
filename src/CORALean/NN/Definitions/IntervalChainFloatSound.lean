import CORALean.NN.Definitions.IntervalChainFloat
import CORALean.NN.Definitions.IntervalChain
import CORALean.NN.Definitions.ScalarEncloses

/-!
# A float interval chain stands for a real one
`Sound c r`: the two chains have the same layers, the float weights and biases read as the real
ones, and each stored activation enclosure encloses the real activation and derivative of `r`
(`ScalarEncloses`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

inductive IntervalChain.Sound :
    ∀ {n k : ℕ}, IntervalChain 𝕋 n k → Real.IntervalChain n k → Prop where
  | nil {n : ℕ} : Sound (.nil : IntervalChain 𝕋 n n) .nil
  | linear {n m k : ℕ} {W : Mat 𝕋 m n} {b : Vec 𝕋 m} {c : IntervalChain 𝕋 m k}
      {r : Real.IntervalChain m k} (h : Sound c r) :
      Sound (.linear W b c) (.linear (toRealMat W) (toRealVec b) r)
  | act {n k : ℕ} {σE σ'E : Interval 𝕋 → Interval 𝕋} {σ σ' : ℝ → ℝ}
      {c : IntervalChain 𝕋 n k} {r : Real.IntervalChain n k} (hσ : ScalarEncloses σE σ)
      (hσ' : ScalarEncloses σ'E σ') (h : Sound c r) :
      Sound (.act σE σ'E c) (.act σ σ' r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
