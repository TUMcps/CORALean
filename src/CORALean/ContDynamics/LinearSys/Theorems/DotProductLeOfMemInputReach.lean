module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec

@[expose] public section

/-!
# The support of what the input reaches, bounded step by step

`w' y` over `y ∈ P^R(t)` is `∫₀ᵗ w' e^{σA} u(t - σ) dσ`. If `w' e^{σA} u ≤ J_i` for every `u ∈ U`
and `σ` in step `i` of `h`, then for `t` in step `j` the integral is at most `Σ_{i<j} h J_i` over
the full steps plus `h max(J_j, 0)` over the part of step `j` up to `t`: CORA.cpp's integral of
the Krylov verification (`integral_ + dt * max(integrand, 0)`).

## Inputs
* `sys` – linear system
* `U` – input set
* `w` – direction
* `h` – step size
* `t` – time
* `j` – the step of `t`
* `J` – bounds of the integrand per step

## Hypotheses
* `hbdd` – input set bounded
* `hh` – step nonnegative
* `hjt` – `t` at or after the start of step `j`
* `htj` – `t` at or before its end
* `hJ` – `J_i` bounds the integrand over step `i`, for `i ≤ j`

## Conclusion
* `w' y ≤ Σ_{i<j} h J_i + h max(J_j, 0)` for every `y ∈ P^R(t)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSetLike Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.dotProduct_le_of_mem_inputReach (sys : LinearSys 𝕋 n) {U : Set (Vec ℝ n)}
    (hbdd : Bornology.IsBounded U) (w : Vec ℝ n) {h t : ℝ} (hh : 0 ≤ h) {j : ℕ}
    (hjt : (j : ℝ) * h ≤ t) (htj : t ≤ ((j : ℝ) + 1) * h) (J : ℕ → ℝ)
    (hJ : ∀ i ≤ j, ∀ σ : ℝ, (i : ℝ) * h ≤ σ → σ ≤ ((i : ℝ) + 1) * h → ∀ u ∈ U,
      w ⬝ᵥ (exp (σ • toRealMat sys.A) *ᵥ u) ≤ J i) : -- --- CONCL ---
    ∀ y ∈ sys.inputReach (S := ExactSet) U t,
      w ⬝ᵥ y ≤ ∑ i ∈ Finset.range j, h * J i + h * max (J j) 0 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  rintro y ⟨u, hu, hmeas, rfl⟩
  have ht : 0 ≤ t := le_trans (mul_nonneg (Nat.cast_nonneg _) hh) hjt
  -- the dot product with `w` as a continuous linear map, through the integral
  set L : Vec ℝ n →L[ℝ] ℝ := ∑ i, w i • ContinuousLinearMap.proj i with hL
  have hLw : ∀ x, L x = w ⬝ᵥ x := fun x => by
    simp [hL, dotProduct]
  have hint := intervalIntegrable_expSub_mulVec (S := ExactSet) (U := U) (A := A) (c := t) ht
    hbdd hu hmeas
  rw [← hLw, ← L.intervalIntegral_comp_comm hint]
  set g : ℝ → ℝ := fun s => L (exp ((t - s) • A) *ᵥ u s) with hg
  have hgint : IntervalIntegrable g volume 0 t :=
    ⟨L.integrable_comp hint.1, L.integrable_comp hint.2⟩
  -- the time from the end, `σ = t - s`
  set φ : ℝ → ℝ := fun σ => g (t - σ) with hφ
  have hsub : ∫ s in (0:ℝ)..t, g s = ∫ σ in (0:ℝ)..t, φ σ := by
    rw [hφ, intervalIntegral.integral_comp_sub_left g t]
    simp
  have hφint : IntervalIntegrable φ volume 0 t := by
    have := hgint.comp_sub_left t
    simp only [sub_zero, sub_self] at this
    exact this.symm
  rw [show (∫ s in (0:ℝ)..t, L (exp ((t - s) • A) *ᵥ u s)) = ∫ s in (0:ℝ)..t, g s from rfl, hsub]
  -- the integrand at `σ ∈ [0, t]` in step `i`
  have hpt : ∀ i ≤ j, ∀ σ, (i : ℝ) * h ≤ σ → σ ≤ ((i : ℝ) + 1) * h → 0 ≤ σ → σ ≤ t →
      φ σ ≤ J i := by
    intro i hi σ h1 h2 h0 hσt
    have hmem : t - σ ∈ Set.Icc (0:ℝ) t := ⟨by linarith, by linarith⟩
    have := hJ i hi σ h1 h2 (u (t - σ)) (hu _ hmem)
    simpa [hφ, hg, hLw, sub_sub_cancel] using this
  have hjh : (j : ℝ) * h ≤ t := hjt
  have hsub' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → IntervalIntegrable φ volume a b := by
    intro a b ha hab hb
    refine hφint.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc ha hb
  -- the full steps, then the part of step `j`
  have hfull : ∑ i ∈ Finset.range j, ∫ σ in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), φ σ
      = ∫ σ in (((0 : ℕ) : ℝ) * h)..((j : ℝ) * h), φ σ :=
    intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * h)
      fun i hi => hsub' _ _ (mul_nonneg (Nat.cast_nonneg _) hh)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hh)
        (le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh) hjh)
  simp only [Nat.cast_zero, zero_mul] at hfull
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hsub' 0 _ le_rfl (mul_nonneg (Nat.cast_nonneg _) hh) hjh)
    (hsub' _ t (mul_nonneg (Nat.cast_nonneg _) hh) hjh le_rfl), ← hfull]
  refine add_le_add (Finset.sum_le_sum fun i hi => ?_) ?_
  · -- a full step is at most `h J_i`
    have hi' : i < j := Finset.mem_range.mp hi
    have hab : (i : ℝ) * h ≤ ((i + 1 : ℕ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hh
    have hend : ((i + 1 : ℕ) : ℝ) * h ≤ t :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hi') hh) hjh
    calc (∫ σ in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), φ σ)
        ≤ ∫ _ in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), J i :=
          intervalIntegral.integral_mono_on hab
            (hsub' _ _ (mul_nonneg (Nat.cast_nonneg _) hh) hab hend) intervalIntegrable_const
            fun σ hσ => hpt i hi'.le σ hσ.1 (by push_cast at hσ; exact hσ.2)
              (le_trans (mul_nonneg (Nat.cast_nonneg _) hh) hσ.1) (le_trans hσ.2 hend)
      _ = h * J i := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
  · -- the part of step `j` up to `t` is at most `h max(J_j, 0)`
    calc (∫ σ in ((j : ℝ) * h)..t, φ σ) ≤ ∫ _ in ((j : ℝ) * h)..t, J j :=
          intervalIntegral.integral_mono_on hjh
            (hsub' _ _ (mul_nonneg (Nat.cast_nonneg _) hh) hjh le_rfl) intervalIntegrable_const
            fun σ hσ => hpt j le_rfl σ hσ.1 (le_trans hσ.2 htj)
              (le_trans (mul_nonneg (Nat.cast_nonneg _) hh) hσ.1) hσ.2
      _ = (t - j * h) * J j := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (t - j * h) * max (J j) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
      _ ≤ h * max (J j) 0 :=
          mul_le_mul_of_nonneg_right (by linarith) (le_max_right _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
