import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntegralPowDivFactorialMul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulPeanoBakerTerm
import CORALean.ContSet.Interval.Real.Theorems.MatPowSmul
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# The `k`-th Peano–Baker term lies in the `k`-th power of the box

When every `A(σ)` lies in the box `B`, `k! P_k(s)` lies in `matPow (s • B) k`:
the iterated integral of `A(σ₁) ⋯ A(σ_k)` over the ordered simplex is that
simplex's volume `s^k/k!` times an average of products of members, and the box
power is convex and holds every such product.

By induction, entry by entry: `P_k(σ)` sits between `σ^k/k!` times `matPow B k`'s
endpoints, `matMul`'s corner products carry that through one more factor `A(σ)`,
and integrating `σ^k/k!` over `[0, s]` gives `s^{k+1}/(k+1)!`. `Interval.matPow_smul`
then reads the scaled endpoints as the box of `s • B`.

A different member at every factor is exactly what `Interval.matPow` admits, so
this is CORA's `expmIndMixed`'s powers made sound for a matrix that varies in time.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Scaling the second pair scales the least corner product. -/
theorem aux_mulLo_scale_snd {a b c d y : ℝ} (hy : 0 ≤ y) :
    Interval.mulLo a b (y * c) (y * d) = y * Interval.mulLo a b c d := by
  have e : ∀ p q : ℝ, p * (y * q) = y * (p * q) := fun p q => by ring
  simp only [Interval.mulLo, e, mul_min_of_nonneg _ _ hy]

/-- The greatest likewise. -/
theorem aux_mulHi_scale_snd {a b c d y : ℝ} (hy : 0 ≤ y) :
    Interval.mulHi a b (y * c) (y * d) = y * Interval.mulHi a b c d := by
  have e : ∀ p q : ℝ, p * (y * q) = y * (p * q) := fun p q => by ring
  simp only [Interval.mulHi, e, mul_max_of_nonneg _ _ hy]

/-- Every entry of `P_k(s)` between `s^k/k!` times `matPow B k`'s endpoints. -/
theorem aux_peanoBakerTerm_between {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) (k : ℕ) :
    ∀ s, 0 ≤ s → ∀ i j,
      s ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B k).inf i j
          ≤ MatExp.peanoBakerTerm A k s i j ∧
        MatExp.peanoBakerTerm A k s i j
          ≤ s ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B k).sup i j := by -- --- PROOF ---
  induction k with
  | zero =>
    intro s _ i j
    simp [MatExp.peanoBakerTerm, Interval.matPow, Interval.point]
  | succ k ih =>
    intro s hs i j
    have hint := MatExp.intervalIntegrable_mul_peanoBakerTerm hA k i j 0 s
    -- pointwise on the window, the integrand sits between the scaled corner sums
    have hpt : ∀ σ ∈ Set.Icc (0:ℝ) s,
        σ ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B (k + 1)).inf i j
            ≤ (A σ * MatExp.peanoBakerTerm A k σ) i j ∧
          (A σ * MatExp.peanoBakerTerm A k σ) i j
            ≤ σ ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B (k + 1)).sup i j := by
      intro σ hσ
      have hc : 0 ≤ σ ^ k / (Nat.factorial k : ℝ) := by have := hσ.1; positivity
      have hB := Interval.mem_mat_iff.mp (hAB σ)
      rw [Matrix.mul_apply]
      show _ * ∑ l : Fin n, Interval.mulLo (B.inf i l) (B.sup i l)
          ((Interval.matPow B k).inf l j) ((Interval.matPow B k).sup l j) ≤ _ ∧
        _ ≤ _ * ∑ l : Fin n, Interval.mulHi (B.inf i l) (B.sup i l)
          ((Interval.matPow B k).inf l j) ((Interval.matPow B k).sup l j)
      rw [Finset.mul_sum, Finset.mul_sum]
      -- one factor in `B`, the other between the scaled bounds of order `k`
      constructor
      · refine Finset.sum_le_sum fun l _ => ?_
        rw [← aux_mulLo_scale_snd hc]
        exact (Interval.mul_between_corners (hB i l).1 (hB i l).2
          (ih σ hσ.1 l j).1 (ih σ hσ.1 l j).2).1
      · refine Finset.sum_le_sum fun l _ => ?_
        rw [← aux_mulHi_scale_snd hc]
        exact (Interval.mul_between_corners (hB i l).1 (hB i l).2
          (ih σ hσ.1 l j).1 (ih σ hσ.1 l j).2).2
    have hmono : ∀ c : ℝ, IntervalIntegrable
        (fun σ : ℝ => σ ^ k / (Nat.factorial k : ℝ) * c) volume 0 s := fun c =>
      (by fun_prop : Continuous fun σ : ℝ => σ ^ k / (Nat.factorial k : ℝ) * c).intervalIntegrable
        _ _
    -- and integrating the scale over the window raises its order by one
    show _ ≤ ∫ σ in (0:ℝ)..s, (A σ * MatExp.peanoBakerTerm A k σ) i j ∧
      ∫ σ in (0:ℝ)..s, (A σ * MatExp.peanoBakerTerm A k σ) i j ≤ _
    rw [← MatExp.integral_pow_div_factorial_mul, ← MatExp.integral_pow_div_factorial_mul]
    exact ⟨intervalIntegral.integral_mono_on hs (hmono _) hint fun σ hσ => (hpt σ hσ).1,
      intervalIntegral.integral_mono_on hs hint (hmono _) fun σ hσ => (hpt σ hσ).2⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k!` times the `k`-th term, at a time `s ≥ 0` of a run inside `B`, lies in
the `k`-th power of the box of the step, `s • B`. -/
theorem MatExp.peanoBakerTerm_mem_matPow {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (Nat.factorial k : ℝ) • MatExp.peanoBakerTerm A k s
      ∈ (Interval.matPow (Interval.smul s B) k).construct := by -- --- PROOF ---
  have hsc := Interval.matPow_smul B hs k
  have hb := aux_peanoBakerTerm_between hA hAB k s hs
  have hf : (0:ℝ) < Nat.factorial k := by positivity
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  rw [hsc.1, hsc.2]
  simp only [Matrix.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hb i j
  -- multiplying the bounds by `k!` cancels the factorial they carry
  constructor
  · calc s ^ k * (Interval.matPow B k).inf i j
        = (Nat.factorial k : ℝ)
          * (s ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B k).inf i j) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hf.le
  · calc _ ≤ (Nat.factorial k : ℝ)
          * (s ^ k / (Nat.factorial k : ℝ) * (Interval.matPow B k).sup i j) :=
          mul_le_mul_of_nonneg_left h2 hf.le
      _ = s ^ k * (Interval.matPow B k).sup i j := by field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
