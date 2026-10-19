module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExponentialRemainder
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `MatExp.expm`

CORA's `@intervalMatrix/expm(intMat, r, maxOrder)`, the exponential of an interval matrix
evaluated dependently: `expmTerms` (the exact terms of order zero to two and the interval powers
over `i!` up to `maxOrder`) plus `exponentialRemainder`. The calls `expm(intMat)` and
`expm(intMat, maxOrder)` are `r = 1`, with `maxOrder = 10` by default. The five-argument call,
which starts the powers elsewhere, is `MatExp.expmFrom`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eI = expm(intMat, r, maxOrder)`: the Taylor terms up to `η`, then the remainder `E`. -/
noncomputable def MatExp.expm (A : Interval (Mat ℝ n n)) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) :=
  -- 4. `eI = eI + E`
  Interval.plus (MatExp.expmTerms A r η) (MatExp.exponentialRemainder A η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
