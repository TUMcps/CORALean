import CORALean.NN.Layers.Operations.Conv
import CORALean.NN.Layers.Theorems.LinearSound
import CORALean.NN.Layers.Theorems.TapMatMulVec

/-!
# What the convolution layer encloses

The convolution the stored kernel denotes, output `j` the weighted sum over its taps plus its
bias: the linear layer's soundness at the stencil, which `tapMat_mulVec` reads row by row.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k c : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.conv_sound (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) (htap : ∀ j, Function.Injective (tap j)) :
    (Layer.conv (S := S) chan tap K b).Sound
      fun x j => (∑ l, toReal (K (chan j) l) * x (tap j l)) + toReal (b j) :=
  (Layer.linear_sound _ b).congr fun x => funext fun j => by
    show (∑ l, toReal (K (chan j) l) * x (tap j l)) + toReal (b j)
      = (toRealMat (tapMat tap fun j l => K (chan j) l) *ᵥ x) j + toRealVec b j
    rw [tapMat_mulVec _ _ htap]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
