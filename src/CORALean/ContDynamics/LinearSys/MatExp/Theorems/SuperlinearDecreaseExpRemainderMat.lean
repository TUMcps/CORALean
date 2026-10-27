module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
public import CORALean.Global.HasSuperlinearDecrease
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `Lemma 1` at eq. (15)-(16)'s own remainder: `E(φΔt,η) ⊆ φ·E(Δt,η)`

[1, Lemma 1]: `∀φ∈(0,1): E(φΔt,η) ⊆ φ E(Δt,η)`, with `E(Δt,η) = [−E_abs(Δt,η), E_abs(Δt,η)]`
(eq. (15)) and `E_abs(Δt,η) = Σ_{k=η+1}^∞ (|A|Δt)^k/k!` (eq. (16)): `MatExp.expRemainderMat`, the
exponential at `|A|Δt` less its Taylor sum through `η`; `E(Δt,η)` itself is
`MatExp.expRemainderInterval`. [1]'s proof, as printed: each entry `Σ_k (|A|φΔt)^k/k!` is
`Σ_k φ^k (|A|Δt)^k/k!`, and `φ^k ≤ φ` for `k ≥ η+1 ≥ 1`. The one hypothesis is `0 ≤ Δt`, which
makes every term non-negative; unlike `superlinearDecrease_expRemainder` there is no convergence
side condition, the series converging for every `Δt`.

## Inputs
* `A` – system matrix
* `η` – Taylor order
* `Δt` – step length

## Hypotheses
* `hΔt` – step length nonnegative

## Conclusion
* the remainder interval matrix shrinks by at least the factor when the step does

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: the interval matrix `[−E_abs(Δt,η), E_abs(Δt,η)]` of eq. (15)-(16) shrinks by
at least `φ` when the step does, for every step `Δt ≥ 0` and every order `η`. -/
theorem MatExp.superlinearDecrease_expRemainderMat (A : Mat ℝ n n) (η : ℕ) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) : -- --- CONCL ---
    HasSuperlinearDecrease (fun δ => MatExp.expRemainderInterval A δ η) Δt := by -- --- PROOF ---
  intro φ hφ M hM
  obtain ⟨hφ0, hφ1⟩ := hφ
  -- entry by entry, the `k`-th term at `φΔt` is `φ^k ≤ φ` times the one at `Δt`
  have hentry : ∀ j k, MatExp.expRemainderMat A (φ * Δt) η j k
      ≤ φ * MatExp.expRemainderMat A Δt η j k := by
    intro j k
    refine hasSum_le (fun i => ?_) (MatExp.hasSum_expRemainderMat_entry A (φ * Δt) η j k)
      ((MatExp.hasSum_expRemainderMat_entry A Δt η j k).mul_left φ)
    have hP : 0 ≤ ((MatExp.absMat A) ^ (i + (η + 1))) j k :=
      (abs_nonneg _).trans (abs_pow_entry_le_absMat_pow_entry A (i + (η + 1)) j k)
    have hterm : 0 ≤ ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
        * ((MatExp.absMat A) ^ (i + (η + 1))) j k := by positivity
    have hpow : φ ^ (i + (η + 1)) ≤ φ :=
      pow_le_of_le_one hφ0.le hφ1.le (Nat.succ_ne_zero _)
    calc ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * (φ * Δt) ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k
        = φ ^ (i + (η + 1)) * (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k) := by rw [mul_pow]; ring
      _ ≤ φ * (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k) := mul_le_mul_of_nonneg_right hpow hterm
  -- `φ⁻¹ • M` is the member of the larger interval matrix that `φ` scales back to `M`
  refine Set.mem_smul_set.mpr ⟨φ⁻¹ • M, fun j k => ?_, ?_⟩
  · have hMjk : |M j k| ≤ φ * MatExp.expRemainderMat A Δt η j k := (hM j k).trans (hentry j k)
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hφ0)]
    calc φ⁻¹ * |M j k| ≤ φ⁻¹ * (φ * MatExp.expRemainderMat A Δt η j k) :=
          mul_le_mul_of_nonneg_left hMjk (inv_nonneg.mpr hφ0.le)
      _ = MatExp.expRemainderMat A Δt η j k := inv_mul_cancel_left₀ hφ0.ne' _
  · rw [smul_smul, mul_inv_cancel₀ hφ0.ne', one_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
