module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiffTight
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# `eDiffTight` is the maximum of the difference of two powers on `[-1,1]`

`|x^a - x^b| ≤ eDiffTight a b`, [1, Prop. 3] as the inequality the relaxation spends. Equal
parity makes the powers those of `|x|` (`(x^a - x^b)² = (|x|^a - |x|^b)²`, as `x^(a+b)` is even),
and on `u ∈ [0,1]` the drift `u^l - u^(l+c) = v^s (1 - v)` with `v = u^c` and `s = l/c` is
bounded by the weighted mean inequality at the weights `s/(s+1)` and `1/(s+1)`, which is where
`(l/h)^(l/c) · (c/h)` comes from.

## Inputs
* `x` – real number
* `a` – first exponent
* `b` – second exponent

## Hypotheses
* `hx` – number is at most one in absolute value

## Conclusion
* the powers differ by at most the tight exponent difference

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `v^s (1 - v) ≤ (l/(l+c))^s · (c/(l+c))` for `s = l/c`, by the weighted mean inequality. -/
theorem PolyZonotope.aux_pow_mul_le (l c : ℕ) (hl : 0 < l) (hc : 0 < c) (v : ℝ) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : -- --- CONCL ---
    v ^ ((l : ℝ) / c) * (1 - v)
      ≤ ((l : ℝ) / (l + c)) ^ ((l : ℝ) / c) * ((c : ℝ) / (l + c)) := by -- --- PROOF ---
  -- the exponent `s = l/c`, and the weighted mean inequality at `s/(s+1)` and `1/(s+1)`
  set s : ℝ := (l : ℝ) / c with hs
  have hs0 : 0 < s := by positivity
  have hs1 : 0 < s + 1 := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := s / (s + 1)) (w₂ := 1 / (s + 1))
    (p₁ := v / s) (p₂ := 1 - v) (by positivity) (by positivity) (by positivity) (by linarith)
    (by field_simp)
  have hrhs : s / (s + 1) * (v / s) + 1 / (s + 1) * (1 - v) = 1 / (s + 1) := by
    field_simp
    ring
  rw [hrhs] at h
  -- raise both sides to the power `s + 1`: the exponents `s/(s+1)` and `1/(s+1)` become `s` and `1`
  have h2 := Real.rpow_le_rpow (by positivity) h hs1.le
  have e1 : ((v / s) ^ (s / (s + 1))) ^ (s + 1) = (v / s) ^ s := by
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have e2 : ((1 - v) ^ (1 / (s + 1))) ^ (s + 1) = 1 - v := by
    rw [← Real.rpow_mul (by linarith)]
    have : 1 / (s + 1) * (s + 1) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (by linarith) _), e1, e2] at h2
  rw [Real.div_rpow hv0 hs0.le] at h2
  -- clear the `s` in `v / s`
  have h3 : v ^ s * (1 - v) ≤ s ^ s * (1 / (s + 1)) ^ (s + 1) := by
    have hss : 0 < s ^ s := Real.rpow_pos_of_pos hs0 _
    have := mul_le_mul_of_nonneg_left h2 hss.le
    calc v ^ s * (1 - v) = s ^ s * (v ^ s / s ^ s * (1 - v)) := by field_simp
      _ ≤ _ := this
  -- the bound is the closed form
  have hK : s ^ s * (1 / (s + 1)) ^ (s + 1) = ((l : ℝ) / (l + c)) ^ s * ((c : ℝ) / (l + c)) := by
    rw [Real.rpow_add_one (by positivity), ← mul_assoc, ← Real.mul_rpow hs0.le (by positivity)]
    have hlc : (l : ℝ) + c ≠ 0 := by positivity
    have hc0 : (c : ℝ) ≠ 0 := by positivity
    have e3 : s * (1 / (s + 1)) = (l : ℝ) / (l + c) := by
      rw [hs]
      field_simp
    have e4 : 1 / (s + 1) = (c : ℝ) / (l + c) := by
      rw [hs]
      field_simp
    rw [e3, e4]
  exact hK ▸ h3

/-- On `u ∈ [0,1]` the drift of `u^l` and `u^(l+c)` is at most the closed form. -/
theorem PolyZonotope.aux_pow_sub_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (l c : ℕ)
    (hc : 0 < c) : -- --- CONCL ---
    |u ^ (l + c) - u ^ l| ≤ if l = 0 then 1 else
      ((l : ℝ) / ((l + c : ℕ) : ℝ)) ^ ((l : ℝ) / (c : ℝ))
        * ((c : ℝ) / ((l + c : ℕ) : ℝ)) := by -- --- PROOF ---
  -- the higher power is the smaller, so the drift is `u^l (1 - u^c)`
  have hle : u ^ (l + c) ≤ u ^ l := pow_le_pow_of_le_one hu0 hu1 (Nat.le_add_right l c)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  have hv0 : 0 ≤ u ^ c := pow_nonneg hu0 _
  have hv1 : u ^ c ≤ 1 := pow_le_one₀ hu0 hu1
  have e : u ^ l - u ^ (l + c) = u ^ l * (1 - u ^ c) := by
    rw [pow_add]
    ring
  split_ifs with hl
  · -- `l = 0`: `1 - u^c ≤ 1`
    subst hl
    simp only [pow_zero, zero_add]
    have := pow_nonneg hu0 c
    linarith
  · -- `l > 0`: the weighted mean bound at `v = u^c`, whose `s`-th power is `u^l`
    have hl0 : 0 < l := Nat.pos_of_ne_zero hl
    have hk := PolyZonotope.aux_pow_mul_le l c hl0 hc (u ^ c) hv0 hv1
    have hpow : (u ^ c) ^ ((l : ℝ) / c) = u ^ l := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0]
      have hc0 : (c : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ hc0, Real.rpow_natCast]
    rw [e, ← hpow]
    push_cast at hk ⊢
    exact hk


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eDiffTight` bounds the difference of two powers of a factor in `[-1,1]`. -/
theorem PolyZonotope.abs_sub_pow_le_eDiffTight {x : ℝ} (hx : |x| ≤ 1) (a b : ℕ) : -- --- CONCL ---
    |x ^ a - x ^ b| ≤ PolyZonotope.eDiffTight a b := by -- --- PROOF ---
  -- the three branches of the closed form
  unfold PolyZonotope.eDiffTight
  split_ifs with hab hpar
  · subst hab
    simp
  · -- different parity: each power alone stays in `[-1,1]`
    have h1 : |x ^ a| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hx
    have h2 : |x ^ b| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hx
    calc |x ^ a - x ^ b| ≤ |x ^ a| + |x ^ b| := abs_sub _ _
      _ ≤ 2 := by linarith
  · -- equal parity: the powers of `|x|` drift the same
    have hpar' : a % 2 = b % 2 := by omega
    have hev : Even (a + b) := by
      rw [Nat.even_add, Nat.even_iff, Nat.even_iff]
      omega
    -- `(x^a - x^b)²` only sees `|x|`, as `a + b` is even
    have hsq : (x ^ a - x ^ b) ^ 2 = (|x| ^ a - |x| ^ b) ^ 2 := by
      have h1 : (x ^ a) ^ 2 = (|x| ^ a) ^ 2 := by rw [← sq_abs (x ^ a), abs_pow]
      have h2 : (x ^ b) ^ 2 = (|x| ^ b) ^ 2 := by rw [← sq_abs (x ^ b), abs_pow]
      have h3 : x ^ a * x ^ b = |x| ^ a * |x| ^ b := by
        rw [← pow_add, ← pow_add, hev.pow_abs]
      rw [sub_sq, sub_sq, h1, h2, mul_assoc 2, mul_assoc 2, h3]
    have habs : |x ^ a - x ^ b| = |(|x|) ^ a - (|x|) ^ b| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rw [habs]
    have hu0 : 0 ≤ |x| := abs_nonneg x
    -- the smaller exponent is `l`, the larger `l + c + 1`
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have hmin : min a (a + c + 1) = a := min_eq_left (by omega)
      have hmax : max a (a + c + 1) = a + (c + 1) := by
        rw [max_eq_right (by omega)]
        ring
      rw [abs_sub_comm]
      have := PolyZonotope.aux_pow_sub_le |x| hu0 hx a (c + 1) (Nat.succ_pos c)
      simp only [hmin, hmax, Nat.add_sub_cancel_left]
      convert this using 3
      simp [add_assoc]
    · -- `b < a`, the same with the roles exchanged
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      have hmin : min (b + c + 1) b = b := min_eq_right (by omega)
      have hmax : max (b + c + 1) b = b + (c + 1) := by
        rw [max_eq_left (by omega)]
        ring
      have := PolyZonotope.aux_pow_sub_le |x| hu0 hx b (c + 1) (Nat.succ_pos c)
      simp only [hmin, hmax, Nat.add_sub_cancel_left]
      convert this using 3
      simp [add_assoc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
