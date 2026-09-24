import CORALean.Global.Float.Instances.Real.Instances
import CORALean.NN.Layers.Definitions.BatchNorm
import CORALean.NN.Layers.Theorems.BatchNormSound

/-!
# The batch normalization layer at the exact fold

ℝ-only: the fold divides by `Real.sqrt`, which no machine scalar computes; a network read in
floats verifies the network its folded numbers describe, which `Layer.batchNorm_sound` covers.

At the scale and shift `Real.batchNormScale`/`Real.batchNormShift` fold from the statistics, the
layer encloses CORA's inference-time formula `γ (x - μ) / √(σ² + ε) + β` per channel.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.OfInterval S] {n c : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.batchNorm_sound (chan : Fin n → Fin c) (gamma beta mean var : Vec ℝ c)
    (eps : ℝ) :
    (CORALean.Layer.batchNorm (S := S) chan (fun k => batchNormScale (gamma k) (var k) eps)
        fun k => batchNormShift (gamma k) (beta k) (mean k) (var k) eps).Sound
      fun x i => gamma (chan i) * (x i - mean (chan i)) / Real.sqrt (var (chan i) + eps)
        + beta (chan i) :=
  (CORALean.Layer.batchNorm_sound _ _ _).congr fun x => funext fun i => by
    show gamma (chan i) * (x i - mean (chan i)) / Real.sqrt (var (chan i) + eps) + beta (chan i)
      = batchNormScale (gamma (chan i)) (var (chan i)) eps * x i
        + batchNormShift (gamma (chan i)) (beta (chan i)) (mean (chan i)) (var (chan i)) eps
    rw [batchNormShift, batchNormScale]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
