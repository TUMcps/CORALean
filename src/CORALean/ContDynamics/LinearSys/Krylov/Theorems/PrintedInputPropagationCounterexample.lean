module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Line 8 of Alg. 2 propagates one step too far

[1, Alg. 2] line 8 sets `R*_{b,k+1} = e^{A(k+1)δ} R*_{b,1}` and line 9 adds its box to the input
part, so after two steps that part is `box(conv(0ₙ, R*_{b,1})) ⊕ box(e^{2Aδ} R*_{b,1})`;
(21)-(22) and (24) at `t_k = kδ` have `e^{Aδ}` there. For `ẋ = -x + u`, `u ∈ [0, 1]`, `δ = 1`,
and line 2 at its tightest, `R*_{b,1} = R_p(1) ⊆ [0, 1 - e⁻¹]`: the two boxes reach at most
`c₀ = 1 - e⁻¹` and `c₁ = e⁻²(1 - e⁻¹)`, and `c₀ + c₁ < 1 - e⁻²`, which the constant input `1`
reaches at `t = 2`. So `R_1 ∪ R_2` (`X₀ = {0}`) misses a reachable state of `[0, 2]`.
Any line 2 enclosing `R_p(1)` gives `R*_{b,1} ⊇ R_p(1)`; the miss is the propagation's.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential of a `1 × 1` matrix is the exponential of its entry. -/
theorem Krylov.aux_exp_one_by_one_entry (M : Mat ℝ 1 1) :
    exp M 0 0 = Real.exp (M 0 0) := by -- --- PROOF ---
  have hM : M = diagonal fun _ => M 0 0 := by
    ext i j
    fin_cases i; fin_cases j
    rfl
  rw [hM, exp_diagonal, diagonal_apply_eq, Pi.exp_def, Real.exp_eq_exp_ℝ]
  rfl

/-- `e^{(c - s)A} v` at `A = -1` is `e^{-(c - s)} v`. -/
theorem Krylov.aux_exp_neg_mulVec (c s : ℝ) (v : Vec ℝ 1) :
    (exp ((c - s) • !![(-1 : ℝ)]) *ᵥ v) 0 = Real.exp (-(c - s)) * v 0 := by -- --- PROOF ---
  have h := Krylov.aux_exp_one_by_one_entry ((c - s) • !![(-1 : ℝ)])
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  simp only [mulVec, dotProduct, Fin.sum_univ_one]
  rw [h]
  norm_num

/-- `∫₀ᶜ e^{-(c - s)} ds = 1 - e^{-c}`. -/
theorem Krylov.aux_integral_exp_neg_sub (c : ℝ) :
    ∫ s in (0 : ℝ)..c, Real.exp (-(c - s)) = 1 - Real.exp (-c) := by -- --- PROOF ---
  have h : (fun s => Real.exp (-(c - s))) = fun s => Real.exp (s - c) := by
    funext s
    ring_nf
  rw [h, intervalIntegral.integral_comp_sub_right (fun x => Real.exp x) c, integral_exp]
  simp

/-- The first coordinate of the input solution at `A = -1`, as a scalar integral. -/
theorem Krylov.aux_coord_integral {c : ℝ} {u : ℝ → Vec ℝ 1}
    (hint : IntervalIntegrable (fun s => exp ((c - s) • !![(-1 : ℝ)]) *ᵥ u s) volume 0 c) :
    (∫ s in (0 : ℝ)..c, exp ((c - s) • !![(-1 : ℝ)]) *ᵥ u s) 0
      = ∫ s in (0 : ℝ)..c, Real.exp (-(c - s)) * u s 0 := by -- --- PROOF ---
  have h := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) hint
  simp only [ContinuousLinearMap.proj_apply] at h
  rw [← h]
  exact intervalIntegral.integral_congr fun s _ => Krylov.aux_exp_neg_mulVec c s (u s)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] line 8 as printed: with `R*_{b,1} = R_p(1)` for `ẋ = -x + u`, `u ∈ [0, 1]`, the
boxes of lines 3 and 8 stay below `c₀` and `c₁`, and `R_p(2)` holds a point beyond `c₀ + c₁`. -/
theorem Krylov.printed_input_propagation_counterexample :
    let A : Mat ℝ 1 1 := !![-1]
    let sys : LinearSys ℝ 1 := ⟨A⟩
    let U : Set (Vec ℝ 1) := {u | 0 ≤ u 0 ∧ u 0 ≤ 1}
    let Rb1 := sys.inputReach (S := 𝒮) U 1           -- line 2, tightest
    let Rb2 := (fun y => exp (((1 + 1 : ℕ) : ℝ) • A) *ᵥ y) '' Rb1          -- line 8 at k = 1
    ∃ y ∈ sys.inputReach (S := 𝒮) U 2, ∃ c₀ c₁ : ℝ,
      0 ≤ c₀ ∧ 0 ≤ c₁ ∧ (∀ x ∈ Rb1, x 0 ≤ c₀) ∧ (∀ x ∈ Rb2, x 0 ≤ c₁)
        ∧ c₀ + c₁ < y 0 := by -- --- PROOF ---
  intro A sys U Rb1 Rb2
  have hbdd : Bornology.IsBounded U := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h : 0 ≤ u 0 ∧ u 0 ≤ 1 := hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  -- every point of `R_p(1)` has first coordinate at most `1 - e⁻¹`
  have hRb1 : ∀ x ∈ Rb1, x 0 ≤ 1 - Real.exp (-1) := by
    rintro _ ⟨u, hu, hmeas, rfl⟩
    have hint := intervalIntegrable_expSub_mulVec (A := !![(-1 : ℝ)]) (c := 1) zero_le_one
      (S := 𝒮) (U := U) hbdd hu hmeas
    -- its first coordinate is integrable, read through the coordinate projection
    have hcomp : IntervalIntegrable (fun s => Real.exp (-(1 - s)) * u s 0) volume 0 1 := by
      have h0 := hint.1
      have h1 := hint.2
      refine ⟨?_, ?_⟩ <;>
        [have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp
            h0;
          have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp
            h1] <;>
        exact h.congr (Filter.Eventually.of_forall fun s => Krylov.aux_exp_neg_mulVec 1 s (u s))
    -- `∫₀¹ e^{-(1-s)} u(s) ds ≤ ∫₀¹ e^{-(1-s)} ds`, as `u ≤ 1`
    show (∫ s in (0 : ℝ)..1, exp ((1 - s) • !![(-1 : ℝ)]) *ᵥ u s) 0 ≤ _
    rw [Krylov.aux_coord_integral hint, ← Krylov.aux_integral_exp_neg_sub 1]
    refine intervalIntegral.integral_mono_on zero_le_one hcomp
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(1 - s))).intervalIntegrable _ _)
      fun s hs => ?_
    have h : 0 ≤ u s 0 ∧ u s 0 ≤ 1 := hu s hs
    exact mul_le_of_le_one_right (Real.exp_pos _).le h.2
  refine ⟨∫ s in (0 : ℝ)..2, exp ((2 - s) • A) *ᵥ (fun _ => 1), ⟨fun _ => fun _ => 1,
    fun _ _ => ⟨zero_le_one, le_rfl⟩, aestronglyMeasurable_const, rfl⟩,
    1 - Real.exp (-1), Real.exp (-2) * (1 - Real.exp (-1)), ?_, ?_, hRb1, ?_, ?_⟩
  · linarith [Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)]
  · have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)
    have := Real.exp_pos (-2)
    nlinarith
  · -- `e^{2A}` scales the first coordinate by `e⁻²`
    rintro _ ⟨x, hx, rfl⟩
    have h := Krylov.aux_exp_neg_mulVec 2 0 x
    show (exp (((1 + 1 : ℕ) : ℝ) • !![(-1 : ℝ)]) *ᵥ x) 0 ≤ _
    rw [show (((1 + 1 : ℕ) : ℝ)) = 2 - 0 by norm_num, h, show -(2 - 0 : ℝ) = -2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hRb1 x hx) (Real.exp_pos _).le
  · -- the constant input reaches `1 - e⁻²`, and `(1 - e⁻¹)(1 + e⁻²) < 1 - e⁻²`
    have hint : IntervalIntegrable
        (fun s => exp ((2 - s) • !![(-1 : ℝ)]) *ᵥ (fun _ => 1 : Vec ℝ 1)) volume 0 2 :=
      ((exp_continuous.comp ((continuous_const.sub continuous_id).smul
        continuous_const)).matrix_mulVec continuous_const).intervalIntegrable _ _
    show (∫ s in (0 : ℝ)..2, exp ((2 - s) • !![(-1 : ℝ)]) *ᵥ (fun _ => 1 : Vec ℝ 1)) 0 > _
    rw [Krylov.aux_coord_integral hint]
    simp only [mul_one]
    rw [Krylov.aux_integral_exp_neg_sub 2]
    -- with `a = e⁻¹`: `(1 - a)(1 + a²) < 1 - a²` is `a(1 - a)² > 0`
    have hsq : Real.exp (-2) = Real.exp (-1) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have h0 : 0 < Real.exp (-1) := Real.exp_pos _
    rw [hsq]
    nlinarith [mul_pos h0 (pow_pos (sub_pos.2 h1) 2)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
