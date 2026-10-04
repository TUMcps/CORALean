import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Taylm.Float.Taylm

/-!
# An array of Taylor models as a layer's set

CORA's `evaluateTaylm` passes a column of `taylm` objects through a network: one model per
neuron, all over the same `d` variables. `TaylmArray 𝕋 d m` is that column, and denotes the
range set `Taylm.construct` gives it, so the shared variables stay shared. The dimension `m` is
the layer's, the number of variables `d` the input's, and a layer maps `TaylmArray 𝕋 d n` to
`TaylmArray 𝕋 d m`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {d : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure TaylmArray (𝕋 : Type) (d m : ℕ) where
  taylm : Fin m → Float.Taylm 𝕋 d

noncomputable instance (m : ℕ) : ContSet (TaylmArray 𝕋 d m) (Vec ℝ m) where
  construct T := Float.Taylm.construct T.taylm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
