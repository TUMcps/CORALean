module

public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# The `ℓ_q` norm is below the `ℓ_p` norm for `p ≤ q`

`[1, App. B]`, the inclusion `B_p ⊆ B_q` of the unit balls of `ℝᵐ` that its rounding of `B_q` by
`B₂` rests on: `‖x‖_q ≤ ‖x‖_p` for `1 ≤ p ≤ q ≤ ∞`, `p` finite. Each coordinate is at most `‖x‖_p`,
so `Σ|xᵢ|^q ≤ ‖x‖_p^{q-p} Σ|xᵢ|^p = ‖x‖_p^q`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp ENNReal

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem lpNorm_le_lpNorm {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (hp : p ≠ ∞)
    (x : Fin m → ℝ) : ‖toLp q x‖ ≤ ‖toLp p x‖ := by -- --- PROOF ---
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := by linarith
  rcases eq_or_ne q ∞ with rfl | hq
  · -- the supremum norm is below every coordinate's bound
    rw [PiLp.norm_eq_ciSup]
    refine Real.iSup_le (fun i => ?_) (norm_nonneg _)
    simpa using PiLp.norm_apply_le (toLp p x) i
  · have hq0 : 0 < q.toReal := by
      have := ENNReal.toReal_mono hq hpq; linarith
    have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
    rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hp0]
    simp only [Real.norm_eq_abs]
    set a := (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) with ha
    have hSp : ∑ i, |x i| ^ p.toReal = a ^ p.toReal := by
      rw [ha, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
      field_simp; simp
    have ha0 : 0 ≤ a := Real.rpow_nonneg (Finset.sum_nonneg fun i _ => by positivity) _
    -- every coordinate is at most `a`
    have hxi : ∀ i, |x i| ≤ a := fun i => by
      have : |x i| ^ p.toReal ≤ a ^ p.toReal := hSp ▸ Finset.single_le_sum
        (f := fun i => |x i| ^ p.toReal) (fun j _ => by positivity) (Finset.mem_univ i)
      exact (Real.rpow_le_rpow_iff (abs_nonneg _) ha0 hp0).mp this
    have hSq : ∑ i, |x i| ^ q.toReal ≤ a ^ q.toReal := by
      calc ∑ i, |x i| ^ q.toReal = ∑ i, |x i| ^ (q.toReal - p.toReal) * |x i| ^ p.toReal := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Real.rpow_add' (abs_nonneg _) (by linarith)]; ring_nf
        _ ≤ ∑ i, a ^ (q.toReal - p.toReal) * |x i| ^ p.toReal := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (hxi i)
              (by linarith)) (by positivity)
        _ = a ^ (q.toReal - p.toReal) * a ^ p.toReal := by rw [← Finset.mul_sum, hSp]
        _ = a ^ q.toReal := by rw [← Real.rpow_add' ha0 (by linarith)]; ring_nf
    calc (∑ i, |x i| ^ q.toReal) ^ (1 / q.toReal) ≤ (a ^ q.toReal) ^ (1 / q.toReal) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) hSq (by positivity)
      _ = a := by rw [← Real.rpow_mul ha0]; field_simp; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
