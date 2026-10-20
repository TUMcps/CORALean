module

public import CORALean.ContSet.Interval.Real.Operations.Powers
public import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter

@[expose] public section

/-!
# `Interval.powers` encloses `M₀ * M ^ k` for every member

Induction on `k` against `matMul_outer`, with `M₀ * M ^ (k + 1) = (M₀ * M ^ k) * M`. The default
call of CORA (`P = A`, `initialOrder = 1`) is `M₀ := M`, giving `M ^ (k + 1)`; `expm` starts at the
exact square (`initialOrder = 2`), whose members are the squares `M * M`.

## Inputs
* `A` – interval matrix
* `P` – initial power
* `M` – member of `A`
* `M₀` – member of `P`
* `k` – step count

## Hypotheses
* `hM` – `M` lies in `A`
* `hM₀` – `M₀` lies in `P`

## Conclusion
* the product `M₀ M ^ k` lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k`-th entry of `powers A P` contains `M₀ * M ^ k` for `M ∈ A` and `M₀ ∈ P`. -/
theorem Interval.powers_outer (A P : Interval (Mat ℝ n n)) {M M₀ : Mat ℝ n n}
    (hM : M ∈ A.construct) (hM₀ : M₀ ∈ P.construct) (k : ℕ) :
    M₀ * M ^ k ∈ (Interval.powers A P k).construct := by -- --- PROOF ---
  induction k with
  | zero => rw [pow_zero, mul_one]; exact hM₀
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact Interval.matMul_outer _ A ih hM

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
