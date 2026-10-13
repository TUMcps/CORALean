module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# The regressor of the dynamic mode decomposition

One column of CORA's `X1 = [X; ones; U]` in `aux_dynamicModeDecomposition`: the state, the
constant `1` that carries the offset `c`, and the input.
The source is [1].

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[x; 1; u]`. -/
def dmdRegressor (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ (n + 1 + m) :=
  Fin.append (Fin.snoc (α := fun _ => ℝ) x 1) u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
