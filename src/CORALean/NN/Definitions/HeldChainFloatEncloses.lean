module

public import CORALean.NN.Definitions.HeldChainFloat
public import CORALean.NN.Definitions.HeldChain
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A float held chain stands for a real one
`Encloses c r`: the two chains have the same layers, and the float weights and slopes read as the
real ones.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A float held chain stands for a real one: the layers agree and the floats read as the reals. -/
inductive HeldChain.Encloses : ∀ {n k : ℕ}, HeldChain 𝕋 n k → Real.HeldChain n k → Prop where
  | nil {n : ℕ} : Encloses (.nil : HeldChain 𝕋 n n) .nil
  | linear {n m k : ℕ} {W : Mat 𝕋 m n} {c : HeldChain 𝕋 m k} {r : Real.HeldChain m k}
      (h : Encloses c r) : Encloses (.linear W c) (.linear (toRealMat W) r)
  | slope {n k : ℕ} {s : Vec 𝕋 n} {c : HeldChain 𝕋 n k} {r : Real.HeldChain n k}
      (h : Encloses c r) : Encloses (.slope s c) (.slope (toRealVec s) r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
