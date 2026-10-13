module

public import CORALean.NN.Layers.Operations.ConvTranspose
public import CORALean.NN.Layers.Theorems.LinearSound
public import CORALean.NN.Layers.Theorems.TapMatMulVec

@[expose] public section

/-!
# What the transposed convolution layer encloses

The exact map the stored kernel denotes: output coordinate `j` collects, from every input `i`,
the weight the helper convolution's row `i` places at `j`, and adds the bias. That is `Wᵀ x + b`
for the helper's stencil `W`, read into ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k c : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.convTranspose_sound (chan : Fin n → Fin c) (tap : Fin n → Fin k → Fin m)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) :
    (Layer.convTranspose (S := S) chan tap K b).Sound
      fun x j => (∑ i, toReal (tapEntry (tap i) (K (chan i)) j) * x i) + toReal (b j) :=
  (Layer.linear_sound _ b).congr fun x => funext fun j => by
    show (∑ i, toReal (tapEntry (tap i) (K (chan i)) j) * x i) + toReal (b j)
      = (toRealMat _ *ᵥ x) j + toRealVec b j
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
