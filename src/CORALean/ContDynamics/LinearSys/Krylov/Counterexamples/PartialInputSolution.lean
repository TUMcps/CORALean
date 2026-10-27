module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The printed input solution over a part of the step fails

[1, Cor. IV.1] with its printed error box `[-1, 1]ⁿ ε̃(tₑ - t₀)` fails at `n = 1`, `A = 3`,
`u = 4`, `δ = 1`, `[t₀, tₑ] = [0, 1/9]`, and Alg. 1 at `ξ = 1` on `C̃ = [3 4; 0 0]`,
`ṽ = [0; 1]`: `Ṽ = ṽ`, `H̃ = 0`, `h₂,₁ = 4`. `P Ṽ = 0`, so the box must hold the whole
`∫₀^{1/9} 4e^{3(1-t)}dt ≥ 4e^{8/3}/9`. Prop. B.1's `ε̃ = h₂,₁ ω ϕ` has `ω = 1` (`e^{H̃t} = 1`) and
`ϕ = (e^{ν} - 1)/ν` at `t_f = δ = 1`, `ν = λ_max(½(C̃ + C̃ᵀ)) = 4`, so `ε̃ = e⁴ - 1`, and
`(e⁴ - 1)/9 < 4e^{8/3}/9` since `e^{4/3} < 4`. The error of `e^{C̃s}ṽ` is not linear in `s` the
way the difference of two of its values would need.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* no admissible error closes the printed partial-step input solution

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential of a `1 × 1` matrix is the exponential of its entry. -/
private theorem Krylov.aux_exp_one_by_one (M : Mat ℝ 1 1) : -- --- CONCL ---
    exp M 0 0 = Real.exp (M 0 0) := by -- --- PROOF ---
  have hM : M = diagonal fun _ => M 0 0 := by
    ext i j
    fin_cases i; fin_cases j
    rfl
  rw [hM, exp_diagonal, diagonal_apply_eq, Pi.exp_def, Real.exp_eq_exp_ℝ]
  rfl

/-- `e^{1/3} < 1.4`, since `1.4³ = 2.744 > e`. -/
private theorem Krylov.aux_exp_third_lt : -- --- CONCL ---
    Real.exp (1 / 3) < 1.4 := by -- --- PROOF ---
  by_contra h
  have h3 : (1.4 : ℝ) ^ 3 ≤ Real.exp (1 / 3) ^ 3 := pow_le_pow_left₀ (by norm_num) (not_lt.1 h) 3
  rw [← Real.exp_nat_mul] at h3
  norm_num at h3
  linarith [Real.exp_one_lt_d9]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. IV.1] as printed: Alg. 1 and Prop. B.1's `ε̃` at `A = 3`, `u = 4`, `δ = 1`, and no
error `r` with `|r| ≤ ε̃(tₑ - t₀)` closes `∫₀^{1/9} e^{A(1-t)}dt u`. -/
theorem Krylov.partial_input_solution_counterexample : -- --- CONCL ---
    let A : Mat ℝ 1 1 := !![3]
    let u : Vec ℝ 1 := ![4]
    let C := Krylov.augment A u
    let v : Fin 2 → ℝ := Pi.single (Fin.last 1) 1
    let K := Krylov.arnoldi C v 1
    let V : Mat ℝ 2 1 := Matrix.of fun i _ => K.1 0 i
    let H : Mat ℝ 1 1 := Matrix.of fun _ _ => K.2 0 0
    let S : Mat ℝ 2 2 := (1 / 2 : ℝ) • (C + Cᵀ)
    let ν : ℝ := 4
    let ε : ℝ := K.2 1 0 * 1 * ((Real.exp (ν * 1) - 1) / (ν * 1))
    (H = 0 ∧ K.2 1 0 = 4 ∧ (∃ x : Fin 2 → ℝ, x ≠ 0 ∧ S *ᵥ x = ν • x)
        ∧ ∀ x : Fin 2 → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ ν * (x ⬝ᵥ x))
      ∧ ¬ ∃ r : Vec ℝ 1, (∀ j, |r j| ≤ ε * (1 / 9 - 0)) ∧
        (∫ t in (0 : ℝ)..(1 / 9), exp ((1 - t) • A) *ᵥ u)
          = (fun j => (V *ᵥ ((exp ((1 - 0) • H) - exp ((1 - 1 / 9) • H)) *ᵥ ![1]))
              (Fin.castSucc j)) + r := by -- --- PROOF ---
  intro A u C v K V H S ν ε
  -- Alg. 1 at `ξ = 1`: `v⁽¹⁾ = ṽ`, `h₁,₁ = ṽᵀC̃ṽ = 0`, `h₂,₁ = ‖C̃ṽ‖ = ‖(4, 0)‖ = 4`
  have hC : C = !![3, 4; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : v = ![0, 1] := by
    ext i
    fin_cases i <;> rfl
  have hnv : ‖v‖₂ = 1 := by
    rw [hv]
    simp [norm₂, Fin.sum_univ_two]
  have hK0 : K.1 0 = v := by
    simp [K, Krylov.arnoldi, hnv]
  have hK00 : K.2 0 0 = 0 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, vecHead, vecTail]
  have hK10 : K.2 1 0 = 4 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_two, vecHead,
      vecTail]
  -- `ν = 4` is the largest eigenvalue of `½(C̃ + C̃ᵀ)`, with eigenvector `(2, 1)`
  have hS : S = !![3, 2; 2, 0] := by
    ext i j
    simp only [S, hC, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num
  refine ⟨⟨?_, hK10, ⟨![2, 1], ?_, ?_⟩, fun x => ?_⟩, ?_⟩
  · ext i j
    simp [H, hK00]
  · intro h
    have := congrFun h 0
    simp at this
  · ext i
    fin_cases i <;> simp [hS, ν, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp only [hS, ν, mulVec, dotProduct, Fin.sum_univ_two]
    simp
    nlinarith [sq_nonneg (x 0 - 2 * x 1)]
  -- the printed box at `j = 0` would have to hold the whole integral, `P Ṽ` being zero
  rintro ⟨r, hr, heq⟩
  have hF : (fun t : ℝ => exp ((1 - t) • A) *ᵥ u)
      = fun t : ℝ => fun _ : Fin 1 => 4 * Real.exp (3 * (1 - t)) := by
    funext t i
    fin_cases i
    simp [mulVec, dotProduct, Krylov.aux_exp_one_by_one, A, u]
    ring_nf
  have hcont : Continuous fun t : ℝ => 4 * Real.exp (3 * (1 - t)) := by fun_prop
  have hint : (∫ t in (0 : ℝ)..(1 / 9), exp ((1 - t) • A) *ᵥ u) 0
      = ∫ t in (0 : ℝ)..(1 / 9), 4 * Real.exp (3 * (1 - t)) := by
    rw [show (fun t : ℝ => exp ((1 - t) • A) *ᵥ u) = _ from hF]
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
      ((continuous_pi fun _ => hcont).intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ)
        (1 / 9))
    exact h.symm
  -- `P Ṽ = 0`: the only Krylov vector is `ṽ = e₂`
  have hV : (V *ᵥ ((exp ((1 - 0) • H) - exp ((1 - 1 / 9) • H)) *ᵥ ![1])) (Fin.castSucc 0) = 0 := by
    simp [V, mulVec, dotProduct, hK0, hv]
  have h0 := congrFun heq 0
  simp only [Pi.add_apply] at h0
  rw [hint, show (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 from rfl] at h0
  rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl, hV, zero_add] at h0
  -- the integrand stays above `4 e^{8/3}` on `[0, 1/9]`
  have hlow : (1 / 9 : ℝ) * (4 * Real.exp (8 / 3))
      ≤ ∫ t in (0 : ℝ)..(1 / 9), 4 * Real.exp (3 * (1 - t)) := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 9)
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => 4 * Real.exp (8 / 3)) MeasureTheory.volume 0 (1 / 9))
      (hcont.intervalIntegrable 0 (1 / 9)) fun t ht => by
        have : (8 / 3 : ℝ) ≤ 3 * (1 - t) := by linarith [ht.2]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    exact hmono
  -- and `ε̃/9 = (e⁴ - 1)/9 < 4e^{8/3}/9`, as `e^{4/3} = e · e^{1/3} < 2.72 · 1.4 < 4`
  have h43 : Real.exp (4 / 3) < 4 := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.exp_add]
    have h1 := Real.exp_one_lt_d9
    have h2 := Krylov.aux_exp_third_lt
    have h3 : 0 < Real.exp (1 / 3) := Real.exp_pos _
    nlinarith [Real.exp_pos 1]
  have h4 : Real.exp 4 = Real.exp (8 / 3) * Real.exp (4 / 3) := by
    rw [← Real.exp_add]; norm_num
  have hε : ε = Real.exp 4 - 1 := by
    simp only [ε, ν, hK10, mul_one]
    ring
  have hr0 := hr 0
  rw [← h0, hε] at hr0
  have := (le_abs_self _).trans hr0
  nlinarith [Real.exp_pos (8 / 3)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
