module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpmMixed
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmFrom
public import CORALean.ContSet.Interval.Real.Operations.MatMul

@[expose] public section

/-!
# `MatExp.expmMixed`

CORA's `@intervalMatrix/expmMixed(intMat, r, intermediateOrder, maxOrder)`: the series split at
`intermediateOrder`. `eI` is the evaluation of `expm` up to that order (`expmTerms`); `eI2` is the
five-argument `expm` (`expmFrom`) from order `intermediateOrder + 1`, started at
`intMat * iPow{intermediateOrder}`, with the remainder after `maxOrder`. CORA refuses an
intermediate order below `2` (`CORA:wrongValue`); here it is a hypothesis of the theorem.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[eI, eI2, iPow, iPow2, E] = expmMixed(intMat, r, k, maxOrder)` without the power arrays. -/
noncomputable def MatExp.expmMixed (A : Interval (Mat ℝ n n)) (r : ℝ) (k η : ℕ) :
    MatExp.ExpmMixed n :=
  -- 1. the powers `iPow{i}` from the exact square of `dependentTerms(intMat * (1 / r), r)`
  let iPow := Interval.powers A (MatExp.dependentTerms (Interval.smul (1 / r) A) r).intSq
  -- 2. `eI = H + Σ_{i = 3 … k} iPow{i} / i!`, the first part of the evaluation
  { eI := MatExp.expmTerms A r k
  -- 3. `eI2` of `expm(intMat, r, maxOrder, k + 1, intMat * iPow{k})`, with the remainder
    eI2 := MatExp.expmFrom A η (k + 1) (Interval.matMul A (iPow (k - 2)))
    E := MatExp.exponentialRemainder A η }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
