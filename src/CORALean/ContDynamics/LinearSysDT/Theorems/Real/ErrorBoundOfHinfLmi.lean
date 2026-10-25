module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.DissipationOfHinfLmi
public import CORALean.Global.UltimateBoundOfRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The `H∞` gain bounds the estimation error

[1, Thm. 3], corrected: if `P ≻ 0` and `Y` satisfy Eq. 16 of [1, Thm. 1], there are
`α, β ∈ (0, 1)` with `‖e_k‖ ≤ √(β (αᵏ V₀ + γ² ‖d‖²_∞ / (1 - α)))`, `k ≥ 1`, for every run of
the error system [1, Eq. 15] at `L = P⁻¹ Y`, `V₀ = e₀ᵀ P e₀`, `‖d‖²_∞` any bound of
`d_kᵀ d_k = w_kᵀw_k + v_kᵀv_k`. The paper prints `<`, which fails for `e₀ = 0`, `d = 0`
(`errorBound_of_hinfLmi_counterexample`). As in the proof: `V_{k+1} ≤ V_k - e_kᵀe_k + γ² d_kᵀd_k`
(its Eq. 29) from Eq. 17 of [1, Thm. 1], then `α₁ I ≼ P ≼ α₂ I` (its Eq. 30) with `α₁ > 1` from
the margin of Eq. 17 and `α₂` the sum of the `|P_ij|`, so `V_{k+1} ≤ α V_k + γ² ‖d‖²_∞`,
`α = 1 - 1/α₂`, unrolled (its Eq. 32), and `β = 1/α₁`.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – disturbance matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Y` – gain variable
* `γ` – attenuation level

## Hypotheses
* `hP` – Lyapunov matrix positive definite
* `h` – the design inequality holds

## Conclusion
* the error bound holds with rates between zero and one

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `xᵀPx ≤ (Σᵢⱼ |Pᵢⱼ|) xᵀx`
theorem LinearSysDT.aux_quad_le_sum_abs (P : Mat ℝ n n) (x : Vec ℝ n) : -- --- CONCL ---
    x ⬝ᵥ (P *ᵥ x) ≤ (∑ i, ∑ j, |P i j|) * (x ⬝ᵥ x) := by -- --- PROOF ---
  have hsq : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i =>
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  -- `P_ij x_i x_j ≤ |P_ij| (x_i² + x_j²)/2 ≤ |P_ij| xᵀx`
  have hterm : ∀ i j, x i * (P i j * x j) ≤ |P i j| * (x ⬝ᵥ x) := fun i j => by
    have h1 := hsq i
    have h2 := hsq j
    have hab : x i * (P i j * x j) ≤ |P i j| * ((x i * x i + x j * x j) / 2) := by
      rcases le_total 0 (P i j) with hp | hp
      · rw [abs_of_nonneg hp]
        nlinarith [mul_nonneg hp (sq_nonneg (x i - x j))]
      · rw [abs_of_nonpos hp]
        nlinarith [mul_nonneg (neg_nonneg.mpr hp) (sq_nonneg (x i + x j))]
    exact hab.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  calc x ⬝ᵥ (P *ᵥ x) = ∑ i, ∑ j, x i * (P i j * x j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |P i j| * (x ⬝ᵥ x) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, ∑ j, |P i j|) * (x ⬝ᵥ x) := by simp only [Finset.sum_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.errorBound_of_hinfLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ : ℝ) (hP : P.PosDef)
    (h : LinearSysDT.IsHinfLmi A C E F P Y γ) : -- --- CONCL ---
    ∃ α β : ℝ, 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      ∀ (e : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ nw) (v : ℕ → Vec ℝ nv) (D : ℝ),
        (∀ k, e (k + 1) = (A - P⁻¹ * Y * C) *ᵥ e k + E *ᵥ w k - (P⁻¹ * Y * F) *ᵥ v k) →
        (∀ k, w k ⬝ᵥ w k + v k ⬝ᵥ v k ≤ D) →
        ∀ k, 1 ≤ k → Real.sqrt (e k ⬝ᵥ e k) ≤
          Real.sqrt (β * (α ^ k * (e 0 ⬝ᵥ (P *ᵥ e 0)) +
            γ ^ 2 * D / (1 - α))) := by -- --- PROOF ---
  obtain ⟨ε, hε, hd⟩ := LinearSysDT.dissipation_of_hinfLmi A C E F P Y γ hP h
  have hPpos : ∀ x : Vec ℝ n, 0 ≤ x ⬝ᵥ (P *ᵥ x) := fun x => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp hP.posSemidef).2 x
  have hxx : ∀ {m : ℕ} (x : Vec ℝ m), 0 ≤ x ⬝ᵥ x := fun x =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  -- Eq. 30 of [1, Thm. 3]: `(1 + ε) xᵀx ≤ xᵀPx ≤ α₂ xᵀx`
  have hlow : ∀ x : Vec ℝ n, (1 + ε) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) := fun x => by
    have := hd x 0 0
    simp only [mulVec_zero, add_zero, sub_zero, dotProduct_zero, mul_zero] at this
    nlinarith [hPpos ((A - P⁻¹ * Y * C) *ᵥ x)]
  set α₂ := max (∑ i, ∑ j, |P i j|) 1 + 1
  have hα₂ : 1 < α₂ := by simp only [α₂]; linarith [le_max_right (∑ i, ∑ j, |P i j|) 1]
  have hup : ∀ x : Vec ℝ n, x ⬝ᵥ (P *ᵥ x) ≤ α₂ * (x ⬝ᵥ x) := fun x =>
    (LinearSysDT.aux_quad_le_sum_abs P x).trans (mul_le_mul_of_nonneg_right
      (by simp only [α₂]; linarith [le_max_left (∑ i, ∑ j, |P i j|) 1]) (hxx x))
  refine ⟨1 - 1 / α₂, 1 / (1 + ε), by
    rw [sub_pos, div_lt_one (by linarith)]; exact hα₂, by
    have : 0 < 1 / α₂ := by positivity
    linarith, by positivity, by rw [div_lt_one (by linarith)]; linarith, ?_⟩
  intro e w v D he hD k hk
  set V : ℕ → ℝ := fun k => e k ⬝ᵥ (P *ᵥ e k)
  have hD0 : 0 ≤ D := (add_nonneg (hxx (w 0)) (hxx (v 0))).trans (hD 0)
  -- Eqs. 29 and 31 of [1, Thm. 3]: `V_{k+1} ≤ V_k - e_kᵀe_k + γ² d_kᵀd_k ≤ α V_k + γ² ‖d‖²_∞`
  have hrec : ∀ k, V (k + 1) ≤ (1 - 1 / α₂) * V k + γ ^ 2 * D := fun k => by
    have h1 := hd (e k) (w k) (v k)
    simp only at h1
    rw [← he k] at h1
    have h2 := mul_le_mul_of_nonneg_left (hD k) (sq_nonneg γ)
    have h3 : V k / α₂ ≤ e k ⬝ᵥ e k := by
      rw [div_le_iff₀ (by linarith)]; linarith [hup (e k)]
    have h4 : 0 ≤ ε * (e k ⬝ᵥ e k + w k ⬝ᵥ w k + v k ⬝ᵥ v k) :=
      mul_nonneg hε.le (add_nonneg (add_nonneg (hxx _) (hxx _)) (hxx _))
    have h5 : (1 - 1 / α₂) * V k = V k - V k / α₂ := by ring
    simp only [V] at h3 h5 ⊢
    linarith
  -- Eq. 32 of [1, Thm. 3], unrolled
  have hα : 0 < 1 / α₂ := by positivity
  have hV := (ultimately_le_of_le_mul_add V (1 - 1 / α₂) (γ ^ 2 * D) (by
    have : 1 / α₂ < 1 := by rw [div_lt_one (by linarith)]; exact hα₂
    linarith) (by linarith) (mul_nonneg (sq_nonneg γ) hD0) hrec).1 k
  -- `e_kᵀe_k ≤ V_k / (1 + ε)`
  have he' : e k ⬝ᵥ e k ≤ 1 / (1 + ε) * V k := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith), mul_comm]
    exact hlow (e k)
  exact Real.sqrt_le_sqrt (he'.trans
    (mul_le_mul_of_nonneg_left hV (by positivity)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
