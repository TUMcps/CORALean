import CORALean.ContDynamics.LinearSys.MatExp.ParticularSolutionOuterCorrelated
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatIsBigO

/-!
# `Δε^U_k`, eq. (25)

`Δε^U_k(Δt,η) := err(e^{Atk}((Σᵢ₌₁^η Ãᵢ)U0 ⊕ E(Δt,η)ΔtU0)) + err(e^{Atk}(⊕ᵢ₌₁^η ÃᵢU0 ⊕
E(Δt,η)ΔtU0))`: eq. (25), the subject of `[1, Lemma 2]`, splits into the correlated and
decorrelated summands, each `err`'d after `e^{Atk}`. Both start at `i0 = 1`, so both
`norm₂_le_of_mem_particularSolutionOuterCorrelated` and
`norm₂_le_of_mem_particularSolutionOuter` give the *same* `Δt`-polynomial bound, and
`particularSolutionErrorBound` is twice it — `err`'s own triangle inequality otherwise unused.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology Asymptotics

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


/-- [1]'s eq. (25): `Δε^U_k(Δt,η)`, the correlated and decorrelated `err`s added. -/
noncomputable def MatExp.particularSolutionError (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  err ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η)
    + err ((fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 1 Δt η)

/-- The `Δt`-polynomial `√n` times which dominates `particularSolutionError` — twice the one
bound both its summands share, since both start their sum at `i0 = 1`. -/
noncomputable def MatExp.particularSolutionErrorBound (A : Mat ℝ n n) (tk : ℝ)
    (U0 : Set (Vec ℝ n)) (Δt : ℝ) (η : ℕ) : ℝ :=
  2 * (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂) *
    ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
      + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Both `err`-summands' underlying sets are within `particularSolutionErrorBound`'s own reach,
half of it each — the same computation `aux_norm₂_le_of_mem_particularSolutionTauError_set` does
for `bPU`, once for the correlated summand and once for the decorrelated one. -/
theorem aux_norm₂_le_of_mem_particularSolutionError_set (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) :
    (∀ z ∈ (fun x => (exp (tk • A)).mulVec x)
          '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η,
        ‖z‖₂ ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) ∧
      (∀ z ∈ (fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 1 Δt η,
        ‖z‖₂ ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) := by -- --- PROOF ---
  have hCnn : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
    Finset.sum_nonneg fun i _ => norm₂_nonneg _
  have heq : MatExp.particularSolutionErrorBound A tk U0 Δt η / 2
      = (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂) *
        ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
            * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
          + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0) := by
    rw [MatExp.particularSolutionErrorBound]; ring
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := MatExp.norm₂_le_of_mem_particularSolutionOuterCorrelated A hU0 1 Δt η y hy
    rw [heq]
    exact (norm₂_mulVec_le _ y).trans (mul_le_mul_of_nonneg_left hy' hCnn)
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := MatExp.norm₂_le_of_mem_particularSolutionOuter A hU0 1 Δt η y hy
    rw [heq]
    exact (norm₂_mulVec_le _ y).trans (mul_le_mul_of_nonneg_left hy' hCnn)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `particularSolutionError` is within its own explicit bound. -/
theorem MatExp.particularSolutionError_le (A : Mat ℝ n n) (tk : ℝ) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) :
    MatExp.particularSolutionError A tk U0 Δt η
      ≤ Real.sqrt n * MatExp.particularSolutionErrorBound A tk U0 Δt η := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := aux_norm₂_le_of_mem_particularSolutionError_set A tk hU0 Δt η
  -- the bound itself is nonnegative, being a sum of products of norms and `err`
  have hr : (0:ℝ) ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2 := by
    have hterm : ∀ i ∈ Finset.Ico 1 (η + 1), (0:ℝ) ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := fun i _ =>
      mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => norm₂_nonneg _)
        (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))) (err_nonneg U0)
    have h1' : (0:ℝ) ≤ ∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := Finset.sum_nonneg hterm
    have h2' : (0:ℝ) ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (abs_nonneg _))
        (err_nonneg U0)
    have h3' : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
      Finset.sum_nonneg fun i _ => norm₂_nonneg _
    rw [MatExp.particularSolutionErrorBound]
    have : (0:ℝ) ≤ 2 * (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂)
        * ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
            * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
          + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  -- `err`'s bridge to a pointwise bound, once for each summand, then folded back together
  have h1'' := err_le_of_forall_norm₂_le hr h1
  have h2'' := err_le_of_forall_norm₂_le hr h2
  rw [MatExp.particularSolutionError]
  have hsplit : Real.sqrt n * MatExp.particularSolutionErrorBound A tk U0 Δt η
      = Real.sqrt n * (MatExp.particularSolutionErrorBound A tk U0 Δt η / 2)
        + Real.sqrt n * (MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) := by ring
  rw [hsplit]
  exact add_le_add h1'' h2''

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
