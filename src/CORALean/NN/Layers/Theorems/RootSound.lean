import CORALean.NN.Layers.Operations.Root
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.RootRelaxationSound

/-!
# What the square root layer encloses

`Real.sqrt` coordinatewise, for every point of every set.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.root_sound (p : ℕ) :
    (Layer.root (𝕋 := 𝕋) (S := S) (n := n) p).Sound fun x i => Real.sqrt (x i) :=
  Layer.activation_sound (rootRelaxation_sound p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
