module

public import CORALean.NN.Operations.WeightAccLayer
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Definitions.WeightNetwork

@[expose] public section

/-!
# `getNormalForm`'s loop

The layers are walked once, linear and elementwise affine layers fused into the accumulator and
identities skipped. At an activation the accumulator is flushed as a layer, and the activation
follows; at the end a non-empty accumulator is flushed and an untouched one dropped.

## Inputs
* none

## Output
* fused network over the remaining layers, started from the accumulator
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The network over the layers still to come, started from the accumulator `acc`. -/
def WeightNetwork.normalFormAux : ∀ {n d k : ℕ}, WeightAcc α n d → WeightNetwork α d k →
    WeightNetwork α n k
  | _, _, _, .id, .nil => .nil
  | _, _, _, .aff W b, .nil => .cons (.linear W b) .nil
  | _, _, _, acc, .cons (.linear W b) rest => normalFormAux (acc.pushLinear W b) rest
  | _, _, _, acc, .cons (.elementwiseAffine s o) rest => normalFormAux (acc.pushAffine s o) rest
  | _, _, _, acc, .cons .identity rest => normalFormAux acc rest
  | _, _, _, acc, .cons (.activation f) rest =>
    .cons acc.layer (.cons (.activation f) (normalFormAux .id rest))  -- flush, then restart

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
