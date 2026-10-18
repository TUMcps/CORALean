module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerTermMemMatPow

@[expose] public section

/-!
# A Peano–Baker term rescaled from `t` to the whole step

`k!` times `(r/t)^k P_k(t)` lies in the `k`-th power of the box of the step,
`r • B`, at `0 < t` and `0 ≤ r`: `peanoBakerTerm_mem_matPow` at `t`, read through
`Interval.matPow_smul` at `t` and at `r`, whose endpoints differ by `(r/t)^k`.

So `P_k(t) = λ^k Q_k` with `Q_k` an order of the step's own Taylor box, `λ = t/r` —
how a time-varying run between the two ends of a step is read as CORA's
interpolation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A term rescaled from `t` to `r`, times `k!`, lies in the `k`-th power of
`r • B`. -/
theorem MatExp.rescaled_peanoBakerTerm_mem_matPow {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) (k : ℕ) {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) : -- --- STMT ---
    (Nat.factorial k : ℝ) • ((r / t) ^ k • MatExp.peanoBakerTerm A k t)
      ∈ (Interval.matPow (Interval.smul r B) k).construct := by -- --- PROOF ---
  have hm := Interval.mem_mat_iff.mp (MatExp.peanoBakerTerm_mem_matPow hA hAB k ht.le)
  have hst := Interval.matPow_smul B ht.le k
  have hsr := Interval.matPow_smul B hr k
  have hq : 0 ≤ (r / t) ^ k := by positivity
  have hscale : (r / t) ^ k * t ^ k = r ^ k := by rw [← mul_pow, div_mul_cancel₀ _ ht.ne']
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  obtain ⟨h1, h2⟩ := hm i j
  rw [hst.1] at h1
  rw [hst.2] at h2
  rw [hsr.1, hsr.2]
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
  -- the bounds at `t` scaled by `(r/t)^k` are the bounds at `r`
  constructor
  · calc r ^ k * (Interval.matPow B k).inf i j
        = (r / t) ^ k * (t ^ k * (Interval.matPow B k).inf i j) := by rw [← hscale]; ring
      _ ≤ (r / t) ^ k * ((Nat.factorial k : ℝ) * MatExp.peanoBakerTerm A k t i j) :=
          mul_le_mul_of_nonneg_left h1 hq
      _ = _ := by ring
  · calc _ = (r / t) ^ k * ((Nat.factorial k : ℝ) * MatExp.peanoBakerTerm A k t i j) := by ring
      _ ≤ (r / t) ^ k * (t ^ k * (Interval.matPow B k).sup i j) :=
          mul_le_mul_of_nonneg_left h2 hq
      _ = r ^ k * (Interval.matPow B k).sup i j := by rw [← hscale]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
