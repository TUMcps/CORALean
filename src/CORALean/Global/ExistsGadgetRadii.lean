module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The radii of the hardness gadget

[1, Lemma 26]: for `n ≥ 2` and `p ∈ (1, ∞)` there are `L ∈ (n - 1, n)` and `ϱ ∈ (0, 1)` with
`1 - ϱᵖ = ((n - ϱ) / L)ᵖ` Eq. 66 of [1, Lemma 26] and
`L = (1 - ((n - ϱ) / L)ᵖ)^{1/p - 1} ((n - ϱ) / L)^{p-1}` Eq. 67 of [1, Lemma 26]. As in the
paper, `ϱ = n^{-1/(p-1)}` and `L = (n - ϱ) / (1 - ϱᵖ)^{1/p}`. The proof there shows `L ≥ n - 1`
and the lemma states `L > n - 1`: the inequalities it splits into are strict for `n ≥ 2`, which
is what is proved. The lemma is stated for `n ∈ ℕ \ {1}`; at `n = 0` no such `L` exists, the right
side of Eq. 67 being positive and `L` negative, so `n ≥ 2` is the hypothesis, the paper's `n > 1`.

## Inputs
* `n` – dimension
* `p` – norm exponent

## Hypotheses
* `hn` – the dimension is at least two
* `hp` – the exponent exceeds one

## Conclusion
* radii `L` and `ϱ` exist in the stated ranges and satisfy both gadget equations

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_gadget_radii (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) : -- --- CONCL ---
    ∃ L ϱ : ℝ, n - 1 < L ∧ L < n ∧ 0 < ϱ ∧ ϱ < 1 ∧ 1 - ϱ ^ p = ((n - ϱ) / L) ^ p ∧
      L = (1 - ((n - ϱ) / L) ^ p) ^ (1 / p - 1) * ((n - ϱ) / L) ^ (p - 1) := by -- --- PROOF ---
  have ha : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 : (1 : ℝ) < n := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  set a : ℝ := (n : ℝ) with hadef
  -- `ϱ = a^{-1/(p-1)}` and `t = ϱᵖ = a^{-p/(p-1)}`, below `1/a ≤ 1/2`
  set ϱ : ℝ := a ^ (-1 / (p - 1)) with hϱ
  have hϱpos : 0 < ϱ := Real.rpow_pos_of_pos (by linarith) _
  have hϱ1 : ϱ < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha1 (by
    have : -1 / (p - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) hp1
    exact this)
  have hϱp : ϱ ^ p = a ^ (-p / (p - 1)) := by
    rw [hϱ, ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  set t : ℝ := ϱ ^ p with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hϱpos _
  -- `t < 1/a ≤ 1/2`: the exponent `-p/(p-1)` is below `-1`
  have ht2 : t < 1 / 2 := by
    have hexp : -p / (p - 1) < -1 := by
      rw [div_lt_iff₀ hp1]
      linarith
    have : a ^ (-p / (p - 1)) < a ^ (-1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt ha1 hexp
    rw [Real.rpow_neg_one] at this
    rw [hϱp]
    calc _ < a⁻¹ := this
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) ha
  -- `ϱ = a t`
  have hϱat : ϱ = a * t := by
    have key : a * a ^ (-p / (p - 1)) = a ^ (-1 / (p - 1)) := by
      calc a * a ^ (-p / (p - 1)) = a ^ (1 : ℝ) * a ^ (-p / (p - 1)) := by rw [Real.rpow_one]
        _ = a ^ (1 + -p / (p - 1)) := (Real.rpow_add (by linarith) _ _).symm
        _ = _ := by
          congr 1
          field_simp
          ring
    rw [hϱp, key]
  -- `s = (1 - t)^{1/p}` and `L = (a - ϱ) / s`
  have h1t : 0 < 1 - t := by linarith
  set s : ℝ := (1 - t) ^ (1 / p) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos h1t _
  have hsp : s ^ p = 1 - t := by
    rw [hs, ← Real.rpow_mul h1t.le, one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hs1 : s < 1 := Real.rpow_lt_one h1t.le (by linarith) (by positivity)
  have haϱ : 0 < a - ϱ := by linarith
  have hratio : (a - ϱ) / ((a - ϱ) / s) = s := by field_simp
  refine ⟨(a - ϱ) / s, ϱ, ?_, ?_, hϱpos, hϱ1, ?_, ?_⟩
  · -- `L > a - 1`: `a - ϱ - (a - 1) s = a (1 - s) + (s - ϱ)`, and `ϱ < s` as `ϱᵖ < sᵖ`
    have hϱs : ϱ < s := by
      by_contra hcon
      have := Real.rpow_le_rpow hspos.le (not_lt.mp hcon) hp0.le
      rw [hsp] at this
      linarith
    rw [lt_div_iff₀ hspos]
    nlinarith
  · -- `L < a`: `a - ϱ = a (1 - t) < a s`, as `1 - t < (1 - t)^{1/p}`
    have h1ts : 1 - t < s := by
      have := Real.rpow_lt_rpow_of_exponent_gt h1t (by linarith : 1 - t < 1)
        (show 1 / p < 1 by rw [div_lt_one hp0]; exact hp)
      rwa [Real.rpow_one] at this
    rw [div_lt_iff₀ hspos]
    nlinarith
  · rw [hratio, hsp]
  · -- Eq. 67: `t^{1/p - 1} = a` and `s^{p-1} = (1 - t) / s`
    rw [hratio, hsp, sub_sub_cancel]
    have htexp : t ^ (1 / p - 1) = a := by
      rw [ht, ← Real.rpow_mul hϱpos.le, hϱ, ← Real.rpow_mul (by linarith)]
      have : -1 / (p - 1) * (p * (1 / p - 1)) = 1 := by
        field_simp
        ring
      rw [this, Real.rpow_one]
    rw [htexp, Real.rpow_sub_one hspos.ne', hsp, hϱat]
    field_simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
