module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Taylm.Float.Taylm

@[expose] public section

/-!
# An array of Taylor models as a layer's set

CORA's `evaluateTaylm` passes a column of `taylm` objects through a network: one model per
neuron, all over the same `d` variables. `TaylmArray 𝕋 d m` is that column, and denotes the
range set `Taylm.construct` gives it, so the shared variables stay shared. The dimension `m` is
the layer's, the number of variables `d` the input's, and a layer maps `TaylmArray 𝕋 d n` to
`TaylmArray 𝕋 d m`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {d : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A column of Taylor models over the same `d` variables, one per neuron. -/
structure TaylmArray (𝕋 : Type) (d m : ℕ) where
  taylm : Fin m → Float.Taylm 𝕋 d

/-- An array of Taylor models denotes the range of the column, so that the shared variables stay
shared. -/
noncomputable instance (m : ℕ) : ContSet (TaylmArray 𝕋 d m) (Vec ℝ m) where
  construct T := Float.Taylm.construct T.taylm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
