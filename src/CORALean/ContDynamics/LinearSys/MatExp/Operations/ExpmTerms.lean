module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTerms
public import CORALean.ContSet.Interval.Real.Operations.Powers
public import CORALean.ContSet.Interval.Real.Operations.Smul
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `MatExp.expmTerms`

The finite part of CORA's `@intervalMatrix/expm`, before the remainder is added: the exact terms
of order zero to two, `H` of `dependentTerms` run on `intMat * (1/r)` with step `r`, plus the
terms `iPow{i} / i!` for `i = 3 … maxOrder`, where the powers start from the exact square and
multiply by `intMat` on the right. `expmMixed` stops this sum at its intermediate order.

## Inputs
* `A` – interval matrix
* `r` – step length
* `η` – Taylor order

## Output
* Taylor terms of the exponential before the remainder is added
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eI` of `expm(intMat, r, maxOrder)` and of `expmMixed` before the remainder is added. -/
noncomputable def MatExp.expmTerms (A : Interval (Mat ℝ n n)) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) :=
  -- 1. the exact terms `[sq, H] = dependentTerms(intMat * (1 / r), r)` of orders zero to two
  let dep := MatExp.dependentTerms (Interval.smul (1 / r) A) r
  -- 2. the powers `iPow{i}`, `i ≥ 2`, from the exact square; `iPow (i - 2)` is `iPow{i}`
  let iPow := Interval.powers A dep.intSq
  -- 3. `eI = H`, then `eI + iPow{i} / i!` for `i = 3 … η`
  (List.range' 3 (η - 2)).foldl
    (fun eI i => Interval.plus eI (Interval.smul ((Nat.factorial i : ℝ)⁻¹) (iPow (i - 2))))
    dep.intH

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
