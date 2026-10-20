module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearReset.synchronize`

CORA's `linearReset/synchronize` for the affine resets `x ↦ W_i x + w_i` of a `Transition`: the
matrices and the offsets are summed, and the coordinates `idStates` add the identity. Returns
`(W, w)`. Real, since the sum of floats is not exact.

## Inputs
* `W` – reset matrices
* `w` – reset offsets
* `idStates` – states kept by identity

## Output
* summed reset matrix and offset
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearReset.synchronize (W : Fin k → Mat ℝ n n) (w : Fin k → Vec ℝ n)
    (idStates : Finset (Fin n)) : Mat ℝ n n × Vec ℝ n :=
  -- `A = ΣA_i + diag(id)`, `c = Σc_i`
  (∑ j, W j + Matrix.diagonal (fun i => if i ∈ idStates then 1 else 0), ∑ j, w j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
