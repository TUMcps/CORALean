import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Theorems.AbsPolyBoundsLe
import CORALean.ContSet.Taylm.Real.Theorems.WeightNonneg
import CORALean.ContSet.Interval.Real.Theorems.AbsMulLoMulHiLe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Taylm.times` keeps the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.8) for the product, whose remainder is the source's
`B(Pₑ) + B(P₁)·I₂ + B(P₂)·I₁ + I₁·I₂` ([1, Def. 2]). The weight is multiplicative over the
product's terms, a dropped term has degree above `N` and so carries `hᴺ⁺¹`, a polynomial's bound
is at most its weight and each remainder at most `C·hᴺ⁺¹`: four summands, each at most
`C₁C₂·hᴺ⁺¹` once `h ≤ 1`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Filtering a list only drops weight. -/
theorem Taylm.aux_weight_filter_le (L : List (ℝ × (Fin n → ℕ))) (p : ℝ × (Fin n → ℕ) → Bool)
    {h : ℝ} (h0 : 0 < h) : Taylm.weight (L.filter p) h ≤ Taylm.weight L h := by -- --- PROOF ---
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.filter_cons]
    have ha : 0 ≤ |a.1| / h ^ Taylm.degree a.2 := div_nonneg (abs_nonneg _) (pow_pos h0 _).le
    split_ifs <;> simp only [Taylm.weight, List.map_cons, List.sum_cons] at ih ⊢ <;> linarith

/-- Terms of degree at least `d` have magnitudes at most `hᵈ` times their weight. -/
theorem Taylm.aux_sum_abs_le_pow_mul_weight (L : List (ℝ × (Fin n → ℕ))) {h : ℝ} {d : ℕ}
    (h0 : 0 < h) (h1 : h ≤ 1) (hd : ∀ a ∈ L, d ≤ Taylm.degree a.2) :
    (L.map fun a => |a.1|).sum ≤ h ^ d * Taylm.weight L h := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.weight]
  | cons a L ih =>
    simp only [Taylm.weight, List.map_cons, List.sum_cons, mul_add] at ih ⊢
    have hp : h ^ Taylm.degree a.2 ≤ h ^ d := pow_le_pow_of_le_one h0.le h1 (hd a (by simp))
    have hpos : 0 < h ^ Taylm.degree a.2 := pow_pos h0 _
    refine add_le_add ?_ (ih fun b hb => hd b (by simp [hb]))
    rw [mul_div_assoc', le_div_iff₀ hpos, mul_comm |a.1|]
    exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-- The weight of the product's terms is the product of the weights. -/
theorem Taylm.aux_weight_mulTerms (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (h : ℝ) :
    Taylm.weight (Taylm.mulTerms L₁ L₂) h =
      Taylm.weight L₁ h * Taylm.weight L₂ h := by -- --- PROOF ---
  induction L₁ with
  | nil => simp [Taylm.weight, Taylm.mulTerms]
  | cons a L ih =>
    simp only [Taylm.weight, Taylm.mulTerms, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons, add_mul] at ih ⊢
    rw [← ih, List.map_map, ← List.sum_map_mul_left]
    congr 1
    -- the degrees add, so the powers of `h` split
    refine congrArg (List.sum (α := ℝ)) (List.map_congr_left fun b _ => ?_)
    simp only [Function.comp, Taylm.degree, Pi.add_apply, Finset.sum_add_distrib, pow_add,
      abs_mul]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.times_scaled {T₁ T₂ : Taylm n} {h C₁ C₂ : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (hN : T₁.maxOrder = T₂.maxOrder) (h₁ : T₁.Scaled h C₁) (h₂ : T₂.Scaled h C₂) :
    (T₁.times T₂).Scaled h (4 * (C₁ * C₂)) := by -- --- PROOF ---
  obtain ⟨w₁, i₁, s₁⟩ := h₁
  obtain ⟨w₂, i₂, s₂⟩ := h₂
  rw [← hN] at i₂ s₂
  have hmax : max T₁.maxOrder T₂.maxOrder = T₁.maxOrder := by rw [hN, max_self]
  have hC₁ : 0 ≤ C₁ := le_trans (Taylm.weight_nonneg _ h0) w₁
  have hC₂ : 0 ≤ C₂ := le_trans (Taylm.weight_nonneg _ h0) w₂
  have hp : 0 ≤ h ^ (T₁.maxOrder + 1) := (pow_pos h0 _).le
  have hp1 : h ^ (T₁.maxOrder + 1) ≤ 1 := pow_le_one₀ h0.le h1
  have hW : Taylm.weight (Taylm.mulTerms T₁.terms T₂.terms) h ≤ C₁ * C₂ := by
    rw [Taylm.aux_weight_mulTerms]
    exact mul_le_mul w₁ w₂ (Taylm.weight_nonneg _ h0) hC₁
  -- the dropped terms have degree above the order, so their magnitudes carry `hᴺ⁺¹`
  have hd : ((((Taylm.mulTerms T₁.terms T₂.terms).filter fun a =>
      !Nat.ble (Taylm.degree a.2) (max T₁.maxOrder T₂.maxOrder))).map fun a => |a.1|).sum
      ≤ h ^ (T₁.maxOrder + 1) * (C₁ * C₂) := by
    refine le_trans (Taylm.aux_sum_abs_le_pow_mul_weight _ (d := T₁.maxOrder + 1) h0 h1
      fun a ha => ?_) ?_
    · have := (List.mem_filter.1 ha).2
      rw [hmax] at this
      simp only [Bool.not_eq_true'] at this
      have : T₁.maxOrder < Taylm.degree a.2 :=
        Nat.lt_of_not_le fun hle => by simp [Nat.ble_eq_true_of_le hle] at this
      omega
    · exact mul_le_mul_of_nonneg_left (le_trans (Taylm.aux_weight_filter_le _ _ h0) hW) hp
  have hD := Taylm.abs_polyBounds_le ((Taylm.mulTerms T₁.terms T₂.terms).filter fun a =>
      !Nat.ble (Taylm.degree a.2) (max T₁.maxOrder T₂.maxOrder))
  -- the polynomials' bounds are at most their weights
  have hB₁ := Taylm.abs_polyBounds_le T₁.terms
  have hB₂ := Taylm.abs_polyBounds_le T₂.terms
  have hs₁ : (T₁.terms.map fun a => |a.1|).sum ≤ C₁ := by
    have := Taylm.aux_sum_abs_le_pow_mul_weight T₁.terms (d := 0) h0 h1 fun _ _ => Nat.zero_le _
    rw [pow_zero, one_mul] at this
    exact le_trans this w₁
  have hs₂ : (T₂.terms.map fun a => |a.1|).sum ≤ C₂ := by
    have := Taylm.aux_sum_abs_le_pow_mul_weight T₂.terms (d := 0) h0 h1 fun _ _ => Nat.zero_le _
    rw [pow_zero, one_mul] at this
    exact le_trans this w₂
  -- the three interval products of the remainder
  have m₁ := Interval.abs_mulLo_mulHi_le (le_trans hB₁.1 hs₁) (le_trans hB₁.2 hs₁) i₂ s₂
  have m₂ := Interval.abs_mulLo_mulHi_le (le_trans hB₂.1 hs₂) (le_trans hB₂.2 hs₂) i₁ s₁
  have m₃ := Interval.abs_mulLo_mulHi_le i₁ s₁ i₂ s₂
  have hq : C₁ * h ^ (T₁.maxOrder + 1) * (C₂ * h ^ (T₁.maxOrder + 1))
      ≤ C₁ * C₂ * h ^ (T₁.maxOrder + 1) := by
    rw [show C₁ * h ^ (T₁.maxOrder + 1) * (C₂ * h ^ (T₁.maxOrder + 1))
      = (C₁ * C₂ * h ^ (T₁.maxOrder + 1)) * h ^ (T₁.maxOrder + 1) by ring]
    exact mul_le_of_le_one_right (by positivity) hp1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Taylm.times]
    refine le_trans (Taylm.aux_weight_filter_le _ _ h0) (le_trans hW ?_)
    linarith [mul_nonneg hC₁ hC₂]
  · simp only [Taylm.times, hmax]
    rw [hmax] at hD hd
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
    linarith [hD.1, m₁.1, m₂.1, m₃.1]
  -- the upper end, the same four summands
  · simp only [Taylm.times, hmax]
    rw [hmax] at hD hd
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
    linarith [hD.2, m₁.2, m₂.2, m₃.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
