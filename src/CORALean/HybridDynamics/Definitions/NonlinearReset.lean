module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Hybrid automata: a nonlinear reset

CORA's `nonlinearReset`: the reset `f(x, u)`, a function of the pre-jump state `x` and an input
`u`, stored as the function itself. CORA's three dimensions `preStateDim`, `inputDim` and
`postStateDim` are the type indices `n`, `m` and `p`; its derivative handles and `tensorOrder`,
which only serve a set-valued evaluation, are not stored (the set-valued `evaluate`, a Taylor
expansion with a remainder, is not here).

Scalar-free, as `Transition`'s reset is not: a nonlinear function of real numbers has no
coefficients to store, so there is no float counterpart.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinearReset (n m p : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
