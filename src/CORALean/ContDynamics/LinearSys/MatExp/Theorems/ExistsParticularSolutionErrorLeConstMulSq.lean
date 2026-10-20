module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatIsBigO
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionErrorLe

@[expose] public section

/-!
# `particularSolutionError` converges to zero superquadratically

[1, Lemma 2]: eventually, as `Δt → 0⁺`, `particularSolutionError` is under one quadratic
bound `K · Δt²`.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `η` – Taylor order

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* the particular solution error is eventually under a constant times the squared step

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

open Matrix NormedSpace Filter Topology Asymptotics

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Eventually, as `Δt → 0⁺`, `particularSolutionError` is under one quadratic bound `K · Δt²`:
`Δt ≤ 1` caps `Δtⁱ⁺¹` (`i ≥ 1`) at `Δt²`, and `Lemma 1`'s rate caps the remainder at a constant
times `Δt`, so every term of `particularSolutionErrorBound` is a constant times `Δt²`. -/
theorem MatExp.exists_particularSolutionError_le_const_mul_sq (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ) :
    ∃ K : ℝ, ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ),
      MatExp.particularSolutionError A tk U0 Δt η ≤ K * Δt ^ 2 := by -- --- PROOF ---
  set CExp := ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ with hCExp
  set CSum := ∑ i ∈ Finset.Ico 1 (η + 1), ∑ j, ‖(fun k => (A ^ i) j k)‖₂ with hCSum
  obtain ⟨cE, hcE⟩ := isBigO_iff.mp (MatExp.expRemainderMat_isBigO A η)
  refine ⟨Real.sqrt n * (2 * CExp) * (CSum * err U0 + (n:ℝ) ^ 2 * max cE 0 * err U0), ?_⟩
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hΔt1 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt ≤ 1 := hid.eventually_le_const (by norm_num)
  filter_upwards [hΔt1, hcE, self_mem_nhdsWithin] with Δt hΔt1 hcE hΔtpos
  have habsΔt : |Δt| = Δt := abs_of_pos hΔtpos
  -- each `Ãᵢ`-summand (`i ≥ 1`) is under `Δt²` once `Δt ≤ 1` caps its own, higher power
  have hterm : ∀ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * Δt ^ 2 * err U0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hfact : (1:ℝ) ≤ (Nat.factorial (i + 1) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) ≤ Δt ^ 2 := by
      rw [habsΔt]
      calc Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) ≤ Δt ^ (i + 1) :=
            div_le_self (pow_nonneg hΔtpos.le _) hfact
        _ ≤ Δt ^ 2 := pow_le_pow_of_le_one hΔtpos.le hΔt1 (by omega)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Finset.sum_nonneg fun j _ => norm₂_nonneg _))
      (err_nonneg U0)
  -- sum `hterm`'s bound over the (fixed, finite) index set
  have hSum : ∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ CSum * Δt ^ 2 * err U0 := by
    calc ∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0
        ≤ ∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * Δt ^ 2 * err U0 :=
          Finset.sum_le_sum hterm
      _ = CSum * Δt ^ 2 * err U0 := by rw [hCSum, Finset.sum_mul, Finset.sum_mul]
  -- `Lemma 1`'s rate bounds `‖expRemainderMat‖` by a constant times `Δtᵂ⁺¹ ≤ Δt`, once `Δt ≤ 1`
  have hE : (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0
      ≤ (n : ℝ) ^ 2 * max cE 0 * err U0 * Δt ^ 2 := by
    rw [habsΔt]
    have hcE' : ‖MatExp.expRemainderMat A Δt η‖ ≤ max cE 0 * Δt ^ (η + 1) := by
      refine hcE.trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (pow_pos hΔtpos _)]
      exact mul_le_mul_of_nonneg_right (le_max_left cE 0) (pow_nonneg hΔtpos.le _)
    have hcap : Δt ^ (η + 1) ≤ Δt := by
      calc Δt ^ (η + 1) ≤ Δt ^ 1 := pow_le_pow_of_le_one hΔtpos.le hΔt1 (by omega)
        _ = Δt := pow_one Δt
    have hstep : ‖MatExp.expRemainderMat A Δt η‖ ≤ max cE 0 * Δt :=
      hcE'.trans (mul_le_mul_of_nonneg_left hcap (le_max_right cE 0))
    calc (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * Δt * err U0
        ≤ (n : ℝ) ^ 2 * (max cE 0 * Δt) * Δt * err U0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hstep (sq_nonneg _)) hΔtpos.le) (err_nonneg U0)
      _ = (n : ℝ) ^ 2 * max cE 0 * err U0 * Δt ^ 2 := by ring
  -- fold both summands' bounds back into `particularSolutionErrorBound`, then into `err`
  have hBound : MatExp.particularSolutionErrorBound A tk U0 Δt η
      ≤ 2 * CExp * (CSum * Δt ^ 2 * err U0 + (n:ℝ) ^ 2 * max cE 0 * err U0 * Δt ^ 2) := by
    rw [MatExp.particularSolutionErrorBound, hCExp]
    have hCExp' : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
      Finset.sum_nonneg fun i _ => norm₂_nonneg _
    exact mul_le_mul_of_nonneg_left (add_le_add hSum hE) (by linarith)
  calc MatExp.particularSolutionError A tk U0 Δt η
      ≤ Real.sqrt n * MatExp.particularSolutionErrorBound A tk U0 Δt η :=
        MatExp.particularSolutionError_le A tk hU0 Δt η
    _ ≤ Real.sqrt n * (2 * CExp * (CSum * Δt ^ 2 * err U0
          + (n:ℝ) ^ 2 * max cE 0 * err U0 * Δt ^ 2)) :=
        mul_le_mul_of_nonneg_left hBound (Real.sqrt_nonneg _)
    _ = Real.sqrt n * (2 * CExp) * (CSum * err U0 + (n:ℝ) ^ 2 * max cE 0 * err U0) * Δt ^ 2 := by
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
