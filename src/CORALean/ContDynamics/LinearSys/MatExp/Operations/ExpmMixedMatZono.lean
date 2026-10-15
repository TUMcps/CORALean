module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpmMixedMatZono
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTermsMatZono
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmFrom
public import CORALean.ContSet.Zonotope.Real.Operations.Powers
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.MatMul

@[expose] public section

/-!
# `MatExp.expmMixedMatZono`

CORA's `@matZonotope/expmMixed(matZ, r, intermediateOrder, maxOrder)`: the series split at
`intermediateOrder`. `eZ` is the dependent evaluation up to that order, `H` of `dependentTerms` plus
the powers of the matrix zonotope from its square; `eI` is the five-argument `expm` (`expmFrom`)
from order `intermediateOrder + 1` at the interval matrix of the zonotope, started at its product
with the last power, with the remainder after `maxOrder`. CORA refuses an intermediate order below
`2` (`CORA:wrongValue`); here it is a hypothesis of the theorem.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[eZ, eI, zPow, iPow, E] = expmMixed(matZ, r, k, maxOrder)` without the power arrays. -/
noncomputable def MatExp.expmMixedMatZono (Z : Zonotope (Mat ℝ n n)) (r : ℝ) (k η : ℕ) :
    MatExp.ExpmMixedMatZono n :=
  -- 1. `[sq, H] = dependentTerms(matZ * (1 / r), r)`
  let dep := MatExp.dependentTermsMatZono (Z.map ((1 / r) • LinearMap.id)) r
  -- 2. the powers `zPow{i}` from the square; `zPow (i - 2)` is `zPow{i}`
  let zPow := Zonotope.powers Z dep.zSq
  -- 3. `eZ = H`, then `eZ + zPow{i} / i!` for `i = 3 … k`
  let eZ := (List.range' 3 (k - 2)).foldl
    (fun eZ i => eZ.plus ((zPow (i - 2)).map ((Nat.factorial i : ℝ)⁻¹ • LinearMap.id))) dep.zH
  -- 4. `intMat = intervalMatrix(matZ)`
  let intMat := Z.interval
  -- 5. `expm(intMat, r, maxOrder, k + 1, intMat * intervalMatrix(zPow{k}))`, and its remainder `E`
  { eZ := eZ
    eI := MatExp.expmFrom intMat η (k + 1) (Interval.matMul intMat (zPow (k - 2)).interval)
    E := MatExp.exponentialRemainder intMat η }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
