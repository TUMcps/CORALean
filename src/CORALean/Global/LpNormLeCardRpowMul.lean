module

public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# The `ℓ_p` norm is below `m^{1/p - 1/q}` times the `ℓ_q` norm

`[1, App. B]`, the inclusion `B_q ⊆ m^{1/p-1/q} B_p` of the unit balls of `ℝᵐ` that its rounding
of `B_q` by `B₂` rests on, with the dimension `m` of the space the balls live in: `‖x‖_p ≤
m^{1/p-1/q} ‖x‖_q` for `1 ≤ p ≤ q ≤ ∞`, `p` finite. The power mean inequality at the exponent
`q/p`; at `q = ∞` each of the `m` coordinates is at most `‖x‖_∞`.

## Inputs
* `p` – smaller exponent
* `q` – larger exponent
* `x` – vector

## Hypotheses
* `hpq` – the exponents are ordered
* `hp` – the smaller exponent is finite

## Conclusion
* the smaller-exponent norm is at most a dimension power times the larger-exponent norm

## References

* [1] [A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC),
      2024.](../../../references/2024/kulmburg-ecc-zonotope-ellipsotope-containment.md)
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

theorem lpNorm_le_card_rpow_mul {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (hp : p ≠ ∞) (x : Fin m → ℝ) : -- --- CONCL ---
    ‖toLp p x‖ ≤ (m : ℝ) ^ (p⁻¹ - q⁻¹).toReal * ‖toLp q x‖ := by -- --- PROOF ---
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [PiLp.norm_eq_sum hp0]
  simp only [Real.norm_eq_abs]
  have hSp0 : 0 ≤ ∑ i, |x i| ^ p.toReal := Finset.sum_nonneg fun i _ => by positivity
  rcases eq_or_ne q ∞ with rfl | hq
  -- the supremum norm
  · -- `Σ|xᵢ|^p ≤ m ‖x‖_∞^p`
    simp only [ENNReal.inv_top, tsub_zero]
    set M := ‖toLp ∞ x‖ with hM
    have hM0 : 0 ≤ M := norm_nonneg _
    have hxi : ∀ i, |x i| ≤ M := fun i => by
      have := PiLp.norm_apply_le (toLp ∞ x) i
      rwa [Real.norm_eq_abs] at this
    have hS : ∑ i, |x i| ^ p.toReal ≤ m * M ^ p.toReal := by
      calc ∑ i, |x i| ^ p.toReal ≤ ∑ _i : Fin m, M ^ p.toReal :=
            Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _) (hxi i) hp0.le
        _ = m * M ^ p.toReal := by simp
    -- take the `p`-th root
    calc (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) ≤ (m * M ^ p.toReal) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow hSp0 hS (by positivity)
      _ = (m : ℝ) ^ (p⁻¹).toReal * M := by
          rw [Real.mul_rpow hm0 (by positivity), ← Real.rpow_mul hM0, ENNReal.toReal_inv]
          field_simp; simp
  · have hq0 : 0 < q.toReal := by
      have := ENNReal.toReal_mono hq hpq; linarith
    have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
    rw [PiLp.norm_eq_sum hq0]
    simp only [Real.norm_eq_abs]
    set Sq := ∑ i, |x i| ^ q.toReal with hSq
    have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun i _ => by positivity
    -- power mean at the exponent `q / p ≥ 1`
    have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := fun i => |x i| ^ p.toReal) (p := q.toReal / p.toReal)
      (by rw [le_div_iff₀ hp0]; linarith) (fun i _ => by positivity)
    simp only [Finset.card_univ, Fintype.card_fin] at hpm
    have hrw : ∀ i, (|x i| ^ p.toReal) ^ (q.toReal / p.toReal) = |x i| ^ q.toReal := fun i => by
      rw [← Real.rpow_mul (abs_nonneg _)]; congr 1; field_simp
    simp only [hrw] at hpm
    -- take the `q`-th root
    have hroot : (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal)
        ≤ ((m : ℝ) ^ (q.toReal / p.toReal - 1) * Sq) ^ (1 / q.toReal) := by
      rw [← Real.rpow_le_rpow_iff (z := q.toReal) (Real.rpow_nonneg hSp0 _)
        (Real.rpow_nonneg (by positivity) _) hq0, ← Real.rpow_mul hSp0,
        ← Real.rpow_mul (by positivity)]
      rw [show 1 / p.toReal * q.toReal = q.toReal / p.toReal by ring,
        show 1 / q.toReal * q.toReal = 1 by field_simp, Real.rpow_one]
      exact hpm
    refine hroot.trans (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg hm0 _) hSq0, ← Real.rpow_mul hm0]
    congr 2
    rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_inv.mpr hpq) (ENNReal.inv_ne_top.mpr
      (by rintro rfl; simp at hp0)), ENNReal.toReal_inv, ENNReal.toReal_inv]
    field_simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
