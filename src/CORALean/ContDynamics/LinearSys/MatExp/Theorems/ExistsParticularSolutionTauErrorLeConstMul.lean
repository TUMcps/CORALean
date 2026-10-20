module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionTauErrorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero

@[expose] public section

/-!
# `particularSolutionTauError` converges to zero superlinearly

[1, Lemma 4]: eventually, as `Δt → 0⁺`, `particularSolutionTauError` is under one linear
bound `K · Δt`.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `η` – Taylor order

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* the τ-form particular solution error is eventually under a constant times the step

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Eventually, as `Δt → 0⁺`, `particularSolutionTauError` is under one linear bound `K · Δt`:
once `Δt ≤ 1` and `‖expRemainderMat A Δt η‖ ≤ 1` (`Lemma 1`'s limit half) cap every higher power
in `particularSolutionTauErrorBound` at `Δt` itself, `K` is `√n` times its `Δt`-free factors. -/
theorem MatExp.exists_particularSolutionTauError_le_const_mul (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ) : -- --- CONCL ---
    ∃ K : ℝ, ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ),
      MatExp.particularSolutionTauError A tk U0 Δt η ≤ K * Δt := by -- --- PROOF ---
  set CExp := ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ with hCExp
  set CSum := ∑ i ∈ Finset.range (η + 1), ∑ j, ‖(fun k => (A ^ i) j k)‖₂ with hCSum
  refine ⟨Real.sqrt n * (CExp * (CSum * err U0 + (n:ℝ) ^ 2 * err U0)), ?_⟩
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hΔt1 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt ≤ 1 := hid.eventually_le_const (by norm_num)
  have hE1 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), ‖MatExp.expRemainderMat A Δt η‖ ≤ 1 :=
    (MatExp.tendsto_expRemainderMat_zero A η).norm.eventually_le_const (by norm_num)
  filter_upwards [hΔt1, hE1, self_mem_nhdsWithin] with Δt hΔt1 hE1 hΔtpos
  have habsΔt : |Δt| = Δt := abs_of_pos hΔtpos
  -- each `Ãᵢ`-summand of the bound is under `Δt` itself once `Δt ≤ 1` caps the higher power
  have hterm : ∀ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * Δt * err U0 := by
    intro i _
    have hpow : |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) ≤ Δt := by
      rw [habsΔt]
      have hfact : (1:ℝ) ≤ (Nat.factorial (i + 1) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      calc Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) ≤ Δt ^ (i + 1) :=
            div_le_self (pow_nonneg hΔtpos.le _) hfact
        _ = Δt ^ i * Δt := by ring
        _ ≤ 1 * Δt := mul_le_mul_of_nonneg_right (pow_le_one₀ hΔtpos.le hΔt1) hΔtpos.le
        _ = Δt := one_mul _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Finset.sum_nonneg fun j _ => norm₂_nonneg _))
      (err_nonneg U0)
  -- sum `hterm`'s bound over the (fixed, finite) index set to bound the whole `Ãᵢ`-sum
  have hSum : ∑ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ CSum * Δt * err U0 := by
    calc ∑ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ ∑ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * Δt * err U0 :=
          Finset.sum_le_sum hterm
      _ = CSum * Δt * err U0 := by rw [hCSum, Finset.sum_mul, Finset.sum_mul]
  have hE : (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0
      ≤ (n : ℝ) ^ 2 * Δt * err U0 := by
    rw [habsΔt]
    have hcap : (n:ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ ≤ (n:ℝ) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hE1 (sq_nonneg _)
    calc (n:ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * Δt * err U0
        ≤ (n:ℝ) ^ 2 * 1 * Δt * err U0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcap hΔtpos.le) (err_nonneg U0)
      _ = (n:ℝ) ^ 2 * Δt * err U0 := by ring
  -- fold both summands' bounds back into `particularSolutionTauErrorBound`, then into `err`
  have hBound : MatExp.particularSolutionTauErrorBound A tk U0 Δt η
      ≤ CExp * (CSum * Δt * err U0 + (n:ℝ) ^ 2 * Δt * err U0) := by
    rw [MatExp.particularSolutionTauErrorBound, hCExp]
    exact mul_le_mul_of_nonneg_left (add_le_add hSum hE)
      (Finset.sum_nonneg fun i _ => norm₂_nonneg _)
  calc MatExp.particularSolutionTauError A tk U0 Δt η
      ≤ Real.sqrt n * MatExp.particularSolutionTauErrorBound A tk U0 Δt η :=
        MatExp.particularSolutionTauError_le A tk hU0 Δt η
    _ ≤ Real.sqrt n * (CExp * (CSum * Δt * err U0 + (n:ℝ) ^ 2 * Δt * err U0)) :=
        mul_le_mul_of_nonneg_left hBound (Real.sqrt_nonneg _)
    _ = Real.sqrt n * (CExp * (CSum * err U0 + (n:ℝ) ^ 2 * err U0)) * Δt := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
