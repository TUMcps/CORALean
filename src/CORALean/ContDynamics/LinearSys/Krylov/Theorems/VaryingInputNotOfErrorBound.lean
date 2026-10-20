module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The varying-input remainder does not follow from the error bound

[1, Thm. IV.2] and [1, Cor. IV.2] enclose `R_p(δ)` by Krylov terms `P Ṽ(u) M e₁` and the box
`[-1, 1]ⁿ{ε̃(u) | u ∈ U}δ`; Appendix A's proof uses of `ε̃(u)` only that it satisfies (3) for the
constant input `u`. That is not enough. At `A = [0 1; 0 0]`, `U = [-1, 1]w`, `w = (1, -1/2)`,
`δ = 8`, Alg. 1 at `ξ = 1` gives `Ṽ(u) = ṽ`, so every Krylov term vanishes. The error of
`e^{C̃t}ṽ` has norm at most `(9/8)t` on `[0, 8]`, so `ε̃(u) = 9/8` satisfies (3) for every
`u ∈ U`, yet the input `-w` on `[0, 6[` and `w` on `[6, 8]` reaches `y₁ = 10 > (9/8)·8`. Prop.
B.1's `ε̃` is far larger here, so this is no counterexample to the printed results with that
`ε̃`; a proof of them has to use more of `ε̃` than (3).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the error bound does not imply the varying-input enclosure

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

/-- A matrix whose cube vanishes: `e^{tM} = I + tM + (t²/2)M²`. -/
theorem Krylov.aux_exp_of_pow_three_eq_zero {m : ℕ} (M : Mat ℝ m m) (hM : M ^ 3 = 0) (t : ℝ) :
    exp (t • M) = 1 + t • M + (t ^ 2 / 2) • M ^ 2 := by -- --- PROOF ---
  have hpow : ∀ k, 3 ≤ k → (t • M) ^ k = 0 := fun k hk => by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [smul_pow, pow_add M, hM, zero_mul, smul_zero]
  rw [exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 3) fun k hk => by
    rw [hpow k (by simp only [Finset.mem_range, not_lt] at hk; omega), smul_zero]]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_pow]
  norm_num [Nat.factorial]
  rw [smul_smul]
  ring_nf

/-- The augmented matrix of `A = [0 1; 0 0]` and `u`. -/
theorem Krylov.aux_augment_nil (u : Vec ℝ 2) :
    Krylov.augment !![(0 : ℝ), 1; 0, 0] u = !![0, 1, u 0; 0, 0, u 1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `e^{tC̃}ṽ - ṽ = (t u₁ + (t²/2) u₂, t u₂, 0)` for the augmented nilpotent matrix. -/
theorem Krylov.aux_exp_augment_nil_mulVec (u : Vec ℝ 2) (t : ℝ) :
    exp (t • Krylov.augment !![(0 : ℝ), 1; 0, 0] u) *ᵥ ![0, 0, 1]
      = ![t * u 0 + t ^ 2 / 2 * u 1, t * u 1, 1] := by -- --- PROOF ---
  rw [Krylov.aux_augment_nil]
  have h3 : (!![0, 1, u 0; 0, 0, u 1; 0, 0, 0] : Mat ℝ 3 3) ^ 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  rw [Krylov.aux_exp_of_pow_three_eq_zero _ h3]
  ext i
  fin_cases i <;>
    simp [sq, mulVec, dotProduct, Fin.sum_univ_three]

/-- The first coordinate of `e^{(8 - s)A}(c w)`, `A = [0 1; 0 0]`, `w = (1, -1/2)`. -/
theorem Krylov.aux_exp_nil_mulVec (c s : ℝ) :
    (exp ((8 - s) • !![(0 : ℝ), 1; 0, 0]) *ᵥ (c • ![1, -1 / 2])) 0
      = c * (s / 2 - 3) := by -- --- PROOF ---
  have h2 : (!![(0 : ℝ), 1; 0, 0]) ^ 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Krylov.aux_exp_of_pow_three_eq_zero _ h2]
  simp [sq, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `∫₀⁸ |s/2 - 3| ds = 10`. -/
theorem Krylov.aux_integral_abs : ∫ s in (0 : ℝ)..8, |s / 2 - 3| = 10 := by -- --- PROOF ---
  have hc : Continuous fun s : ℝ => |s / 2 - 3| := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 6) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  -- the absolute value resolved on each side of `6`
  have h1 : ∫ s in (0 : ℝ)..6, |s / 2 - 3| = ∫ s in (0 : ℝ)..6, (3 - s / 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    rw [abs_of_nonpos (by linarith [hs.2])]
    ring
  have h2 : ∫ s in (6 : ℝ)..8, |s / 2 - 3| = ∫ s in (6 : ℝ)..8, (s / 2 - 3) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact abs_of_nonneg (by linarith [hs.1])
  -- `∫₀⁶ (3 - s/2) ds = 9` and `∫₆⁸ (s/2 - 3) ds = 1`
  have hlin : IntervalIntegrable (fun s : ℝ => s / 2) volume 0 6 ∧
      IntervalIntegrable (fun s : ℝ => s / 2) volume 6 8 :=
    ⟨(by fun_prop : Continuous fun s : ℝ => s / 2).intervalIntegrable _ _,
      (by fun_prop : Continuous fun s : ℝ => s / 2).intervalIntegrable _ _⟩
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const hlin.1,
    intervalIntegral.integral_sub hlin.2 intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_div, integral_id, integral_id,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. IV.2] and [1, Cor. IV.2] do not follow from (3): at `ξ = 1` every Krylov term
`P Ṽ(u) M e₁` is zero, `ε̃ = 9/8` satisfies (3) for every `u ∈ U` on `[0, δ]`, and `R_p(δ)` has
a point outside `[-1, 1]ⁿ ε̃ δ`. -/
theorem Krylov.varying_input_not_of_errorBound : -- --- CONCL ---
    let A : Mat ℝ 2 2 := !![0, 1; 0, 0]
    let w : Vec ℝ 2 := ![1, -1 / 2]
    let U : Set (Vec ℝ 2) := {u | ∃ β ∈ Set.Icc (-1 : ℝ) 1, u = β • w}
    let v : Fin 3 → ℝ := Pi.single (Fin.last 2) 1
    let δ : ℝ := 8
    let ε : ℝ := 9 / 8
    (∀ u ∈ U, (∀ i : Fin 2,
        Krylov.arnoldiBasis (Krylov.augment A u) v 1 (Fin.castSucc i) 0 = 0)
      ∧ ∀ t ∈ Set.Icc 0 δ,
        ‖exp (t • Krylov.augment A u) *ᵥ v - Krylov.arnoldiBasis (Krylov.augment A u) v 1 *ᵥ
            (exp (t • Krylov.arnoldiHessenberg (Krylov.augment A u) v 1) *ᵥ Pi.single 0 1)‖₂
          ≤ ‖v‖₂ * ε * t)
      ∧ ∃ y ∈ (LinearSys.canonical A : LinearSys ℝ 2).inputReach (S := 𝒮) U δ,
          ε * δ < |y 0| := by -- --- PROOF ---
  intro A w U v δ ε
  have hv : v = ![0, 0, 1] := by
    ext i
    fin_cases i <;> rfl
  have hnv : ‖v‖₂ = 1 := by
    rw [hv]
    simp [norm₂, Fin.sum_univ_three]
  refine ⟨fun u hu => ?_, ?_⟩
  · -- Alg. 1 at `ξ = 1`: `v⁽¹⁾ = ṽ` and `h₁,₁ = ṽᵀC̃ṽ = 0`
    obtain ⟨β, hβ, rfl⟩ := hu
    have hK0 : (Krylov.arnoldi (Krylov.augment A (β • w)) v 1).1 0 = v := by
      simp [Krylov.arnoldi, hnv]
    have hV : Krylov.arnoldiBasis (Krylov.augment A (β • w)) v 1 = Matrix.of fun i _ => v i := by
      ext i k
      fin_cases k
      simp [Krylov.arnoldiBasis, hK0]
    have hH : Krylov.arnoldiHessenberg (Krylov.augment A (β • w)) v 1 = 0 := by
      ext i k
      fin_cases i; fin_cases k
      simp [Krylov.arnoldiHessenberg, Krylov.arnoldi, Krylov.gramSchmidtStep, hv, A,
        Krylov.aux_augment_nil, dotProduct, Fin.sum_univ_three]
    -- `P Ṽ = 0`, and the error is `e^{C̃t}ṽ - ṽ`
    refine ⟨fun i => ?_, fun t ht => ?_⟩
    · rw [hV, hv]
      fin_cases i <;> rfl
    · rw [hV, hH, smul_zero, exp_zero, one_mulVec, hnv, hv, Krylov.aux_exp_augment_nil_mulVec]
      have hcol : (Matrix.of fun i (_ : Fin 1) => (![0, 0, 1] : Fin 3 → ℝ) i) *ᵥ
          (Pi.single 0 1 : Fin 1 → ℝ) = ![0, 0, 1] := by
        ext i
        fin_cases i <;> simp [mulVec, dotProduct]
      rw [hcol]
      -- `‖(β(t - t²/4), -βt/2, 0)‖₂² ≤ (5/4)t² ≤ ((9/8)t)²`
      have ht0 : 0 ≤ t := ht.1
      have ht8 : t ≤ 8 := ht.2
      have hβ2 : β ^ 2 ≤ 1 := by nlinarith [hβ.1, hβ.2]
      have hsq : (t * (β • w) 0 + t ^ 2 / 2 * (β • w) 1) ^ 2 + (t * (β • w) 1) ^ 2
          ≤ (1 * ε * t) ^ 2 := by
        simp only [w, ε, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        have h1 : (1 - t / 4) ^ 2 ≤ 1 := by nlinarith
        have : (t * (β * 1) + t ^ 2 / 2 * (β * (-1 / 2))) ^ 2 + (t * (β * (-1 / 2))) ^ 2
            = β ^ 2 * t ^ 2 * ((1 - t / 4) ^ 2 + 1 / 4) := by ring
        rw [this]
        have hb : β ^ 2 * t ^ 2 * ((1 - t / 4) ^ 2 + 1 / 4) ≤ 1 * t ^ 2 * (5 / 4) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hβ2 (sq_nonneg t)) (by linarith)
            (by positivity) (by positivity)
        nlinarith [sq_nonneg t]
      rw [norm₂, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 * ε * t)]
      refine Real.sqrt_le_sqrt ?_
      simpa [Fin.sum_univ_three] using hsq
  · -- the input `-w` on `[0, 6[` and `w` on `[6, 8]`
    let c : ℝ → ℝ := fun s => if s < 6 then -1 else 1
    have hcm : Measurable c := Measurable.ite measurableSet_Iio measurable_const measurable_const
    have hU : ∀ s ∈ Set.Icc (0 : ℝ) δ, c s • w ∈ U := fun s _ =>
      ⟨c s, by by_cases h : s < 6 <;> simp [c, h], rfl⟩
    have hmeas : AEStronglyMeasurable (fun s => c s • w) (volume.restrict (Set.Icc 0 δ)) :=
      (hcm.smul_const w).aestronglyMeasurable
    have hbdd : Bornology.IsBounded U := by
      refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
      obtain ⟨β, hβ, rfl⟩ := hu
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      have hw : ‖w‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        fin_cases i <;> norm_num [w]
      have : ‖β‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; exact hβ
      nlinarith [norm_nonneg w, norm_nonneg β]
    refine ⟨_, ⟨fun s => c s • w, hU, hmeas, rfl⟩, ?_⟩
    have hint := intervalIntegrable_expSub_mulVec (A := A) (c := δ) (by norm_num : (0 : ℝ) ≤ δ)
      (S := 𝒮) (U := U) hbdd hU hmeas
    -- the first coordinate, read through the coordinate projection
    have hproj := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) hint
    simp only [ContinuousLinearMap.proj_apply] at hproj
    show ε * δ < |(∫ s in (0 : ℝ)..δ, exp ((δ - s) • A) *ᵥ (c s • w)) 0|
    rw [← hproj]
    have hpt : ∀ s, (exp ((δ - s) • A) *ᵥ (c s • w)) 0 = |s / 2 - 3| := fun s => by
      rw [show δ = 8 from rfl, Krylov.aux_exp_nil_mulVec]
      by_cases h : s < 6
      · simp only [c, h, if_true]
        rw [abs_of_neg (by linarith)]
        ring
      · simp only [c, h, if_false]
        rw [abs_of_nonneg (by linarith)]
        ring
    simp only [hpt]
    rw [show δ = 8 from rfl, Krylov.aux_integral_abs]
    norm_num [ε]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
