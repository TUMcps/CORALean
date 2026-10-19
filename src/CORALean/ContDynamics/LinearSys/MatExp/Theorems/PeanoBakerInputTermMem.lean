module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousPeanoBakerInputTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntegralMemSmulOfMemSmul
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntegralPowDivFactorialMul
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemPoint
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# The `k`-th Peano–Baker term of an input, inside the `k`-th box power of its set

When every `A(σ)` lies in `B` and every `u(σ)` in `U`, `V_k(s)` lies in
`s^{k+1}/(k+1)!` times the closed convex hull of `matPow B k` applied to `U`:
the simplex of `k + 1` times has that volume, and the integrand is a product of
`k` members and an input, which the box power applied to `U` holds.

The hull is the point. `{N v}` for `N` in a box and `v ∈ U` is not convex, and an
average of such products need not be one; its closed convex hull is, and a member
of `B` maps the hull of order `k` into that of order `k + 1`, being linear and
continuous. So the induction runs on the hull, and
`integral_mem_smul_of_mem_smul` carries it through each integral.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A member of `B` maps the hull of order `k` into the hull of order `k + 1`. -/
theorem aux_mulVec_mem_hull {B : Interval (Mat ℝ n n)} {U : Set (Vec ℝ n)} {M : Mat ℝ n n}
    (hM : M ∈ B.construct) {k : ℕ} {y : Vec ℝ n}
    (hy : y ∈ closure (convexHull ℝ
      {z | ∃ N ∈ (Interval.matPow B k).construct, ∃ v ∈ U, z = N *ᵥ v})) : -- --- CONCL ---
    M *ᵥ y ∈ closure (convexHull ℝ
      {z | ∃ N ∈ (Interval.matPow B (k + 1)).construct, ∃ v ∈ U, z = N *ᵥ v}) := by -- --- PROOF ---
  have hc : Continuous (Matrix.mulVecLin M) := (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have h := image_closure_subset_closure_image hc (Set.mem_image_of_mem _ hy)
  rw [LinearMap.image_convexHull] at h
  refine closure_mono (convexHull_mono ?_) h
  -- one more factor in the box is one more order of the power
  rintro _ ⟨_, ⟨N, hN, v, hv, rfl⟩, rfl⟩
  exact ⟨M * N, Interval.matMul_outer B (B.matPow k) hM hN, v, hv,
    by simp [Matrix.mulVec_mulVec]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `V_k(s)` is `s^{k+1}/(k+1)!` times a point of the closed convex hull of the
`k`-th box power applied to the input set. -/
theorem MatExp.peanoBakerInputTerm_mem {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {u : ℝ → Vec ℝ n}
    (hu : ∀ a b, IntervalIntegrable u volume a b) {U : Set (Vec ℝ n)} {t : ℝ} (ht : 0 ≤ t)
    (huU : ∀ s ∈ Set.Icc 0 t, u s ∈ U) (k : ℕ) : -- --- CONCL ---
    ∀ s ∈ Set.Icc 0 t, MatExp.peanoBakerInputTerm A u k s
      ∈ (s ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • closure (convexHull ℝ
        {z | ∃ N ∈ (Interval.matPow B k).construct, ∃ v ∈ U, z = N *ᵥ v}) := by -- --- PROOF ---
  -- the hull at every order is closed, convex and holds a point
  have hne : ∀ k, (closure (convexHull ℝ
      {z | ∃ N ∈ (Interval.matPow B k).construct, ∃ v ∈ U, z = N *ᵥ v})).Nonempty := fun k =>
    ⟨_, subset_closure (subset_convexHull ℝ _
      ⟨A 0 ^ k, Interval.matPow_outer B (hAB 0) k, u 0, huU 0 ⟨le_rfl, ht⟩, rfl⟩)⟩
  have hcv : ∀ k, Convex ℝ (closure (convexHull ℝ
      {z | ∃ N ∈ (Interval.matPow B k).construct, ∃ v ∈ U, z = N *ᵥ v})) := fun _ =>
    (convex_convexHull ℝ _).closure
  -- the weight `σ^k/k!`, whose integral is the next order's
  have hw : ∀ k : ℕ, IntervalIntegrable
      (fun σ : ℝ => σ ^ k / (Nat.factorial k : ℝ) * 1) volume 0 t := fun k =>
    (by fun_prop : Continuous fun σ : ℝ => σ ^ k / (Nat.factorial k : ℝ) * 1).intervalIntegrable
      _ _
  -- at the start of the window every term is zero
  have hzero : ∀ k, ∀ s ∈ Set.Icc 0 t, s = 0 → MatExp.peanoBakerInputTerm A u k s
      ∈ (s ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • closure (convexHull ℝ
        {z | ∃ N ∈ (Interval.matPow B k).construct, ∃ v ∈ U, z = N *ᵥ v}) := by
    rintro k s - rfl
    cases k <;> simp [MatExp.peanoBakerInputTerm, Set.zero_smul_set (hne _)]
  -- every window inside the whole one, and the identity the zeroth power
  have hsub : ∀ s ∈ Set.Icc 0 t, Set.uIcc 0 s ⊆ Set.uIcc 0 t := fun s hs => by
    rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le ht]; exact Set.Icc_subset_Icc le_rfl hs.2
  have h1 : (1 : Mat ℝ n n) ∈ (Interval.matPow B 0).construct := Interval.mem_point 1
  induction k with
  | zero =>
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · exact hzero 0 s hs h0.symm
    -- the input itself is in the hull of order `0`, at weight one
    have h := integral_mem_smul_of_mem_smul (hcv 0) isClosed_closure hs.1 (hu 0 s)
      ((hw 0).mono_set (hsub s hs))
      (fun σ _ => by positivity) (fun σ hσ => by
        have hm : u σ ∈ closure (convexHull ℝ
            {z | ∃ N ∈ (Interval.matPow B 0).construct, ∃ v ∈ U, z = N *ᵥ v}) :=
          subset_closure (subset_convexHull ℝ _
            ⟨1, h1, u σ, huU σ ⟨hσ.1, hσ.2.trans hs.2⟩, by simp⟩)
        simpa using hm)
      (by rw [MatExp.integral_pow_div_factorial_mul]; positivity)
    rwa [MatExp.integral_pow_div_factorial_mul, mul_one] at h
  | succ k ih =>
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · exact hzero (k + 1) s hs h0.symm
    -- each integrand is the scaled hull of order `k` mapped by a member of `B`
    have h := integral_mem_smul_of_mem_smul (hcv (k + 1)) isClosed_closure hs.1
      (MatExp.intervalIntegrable_mulVec hA
        (MatExp.continuous_peanoBakerInputTerm hA hu k).continuousOn)
      ((hw (k + 1)).mono_set (hsub s hs))
      (fun σ hσ => by have := hσ.1; positivity) (fun σ hσ => by
        obtain ⟨y, hy, hyV⟩ := ih σ ⟨hσ.1, hσ.2.trans hs.2⟩
        rw [mul_one, ← hyV, Matrix.mulVec_smul]
        exact Set.smul_mem_smul_set (aux_mulVec_mem_hull (hAB σ) hy))
      (by rw [MatExp.integral_pow_div_factorial_mul]; positivity)
    rwa [MatExp.integral_pow_div_factorial_mul, mul_one] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
