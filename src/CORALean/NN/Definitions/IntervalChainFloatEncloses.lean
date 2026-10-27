module

public import CORALean.NN.Definitions.IntervalChainFloat
public import CORALean.NN.Definitions.IntervalChain
public import CORALean.NN.Definitions.Basic

@[expose] public section

/-!
# A float interval chain stands for a real one
`Encloses c r`: the two chains have the same layers, the float weights and biases read as the real
ones, and each stored activation enclosure encloses the real activation and derivative of `r`
(`EnclosesScalar`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A float interval chain stands for a real one: the layers agree, the float weights read as the
real ones, and each stored enclosure encloses the real activation and its derivative. -/
inductive IntervalChain.Encloses :
    ∀ {n k : ℕ}, IntervalChain 𝕋 n k → Real.IntervalChain n k → Prop where
  | nil {n : ℕ} : Encloses (.nil : IntervalChain 𝕋 n n) .nil
  | linear {n m k : ℕ} {W : Mat 𝕋 m n} {b : Vec 𝕋 m} {c : IntervalChain 𝕋 m k}
      {r : Real.IntervalChain m k} (h : Encloses c r) :
      Encloses (.linear W b c) (.linear (toRealMat W) (toRealVec b) r)
  | act {n k : ℕ} {σE σ'E : Interval 𝕋 → Interval 𝕋} {σ σ' : ℝ → ℝ}
      {c : IntervalChain 𝕋 n k} {r : Real.IntervalChain n k} (hσ : EnclosesScalar σE σ)
      (hσ' : EnclosesScalar σ'E σ') (h : Encloses c r) :
      Encloses (.act σE σ'E c) (.act σ σ' r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
