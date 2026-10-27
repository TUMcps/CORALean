module

public import CORALean.ContSet.Interval.Float.Operations.Powers
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter

@[expose] public section

/-!
# `Interval.powers` contains the matrix powers

Each power is the rounded product of the previous one with `A`, so `M₀ * M ^ k` stays inside by
`Interval.matMul_outer`.

## Inputs
* `A` – interval matrix
* `P` – initial power
* `M` – member of `A`
* `M₀` – member of `P`
* `k` – offset

## Hypotheses
* `hM` – `M` lies in `A`
* `hM₀` – `M₀` lies in `P`

## Conclusion
* `M₀ * M ^ k` lies in the power at offset `k`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.powers_outer (A P : Interval (Mat 𝕋 n n)) {M M₀ : Mat ℝ n n}
    (hM : M ∈ A.construct) (hM₀ : M₀ ∈ P.construct) (k : ℕ) : -- --- CONCL ---
    M₀ * M ^ k ∈ (Interval.powers A P k).construct := by -- --- PROOF ---
  induction k with
  | zero => rw [pow_zero, mul_one]; exact hM₀
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact Interval.matMul_outer _ A ih hM

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
