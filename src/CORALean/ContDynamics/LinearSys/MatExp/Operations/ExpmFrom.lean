module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExponentialRemainder
public import CORALean.ContSet.Interval.Real.Operations.Powers
public import CORALean.ContSet.Interval.Real.Operations.Smul
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `MatExp.expmFrom`

The five-argument call of CORA's `@intervalMatrix/expm(intMat, r, maxOrder, initialOrder,
initialPower)`: `eI` starts at `initialPower / initialOrder!`, the powers continue from
`initialPower` by right multiplication with `intMat`, the terms `initialOrder + 1 … maxOrder` are
added, and the remainder closes the series. `expmMixed` calls it for the part of the series past its
intermediate order. The time step `r` is unused in this branch, so it is not an argument.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `expm(intMat, r, η, k, P)`: the series from order `k`, whose power `Aᵏ` is enclosed by `P`. -/
noncomputable def MatExp.expmFrom (A : Interval (Mat ℝ n n)) (η k : ℕ)
    (P : Interval (Mat ℝ n n)) : Interval (Mat ℝ n n) :=
  -- 1. `eI = initialPower * (1 / factorial(initialOrder))`
  let eI₀ := Interval.smul ((Nat.factorial k : ℝ)⁻¹) P
  -- 2. the powers `iPow{i}` from the initial power; `iPow (i - k)` is `iPow{i}`
  let iPow := Interval.powers A P
  -- 3. `eI = eI + iPow{i} / i!` for `i = initialOrder + 1 … η`
  let eI := (List.range' (k + 1) (η - k)).foldl
    (fun eI i => Interval.plus eI (Interval.smul ((Nat.factorial i : ℝ)⁻¹) (iPow (i - k)))) eI₀
  -- 4. `eI = eI + E`
  Interval.plus eI (MatExp.exponentialRemainder A η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
