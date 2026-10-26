module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Taylm.Float.Operations.Smul
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul

@[expose] public section

/-!
# `Taylm.smul` encloses the scaled function

For every factor in `[alo, ahi]`: the remainder and the error box by their corner products, each
corner of the sum `a (r + e)` being at least the sum of the least corners (`aux_mul_sum_between`),
and the stored coefficients by `abs_polyOf_round_le`, whose cost goes into the box.

## Inputs
* `alo` – lower end of the scalar
* `ahi` – upper end of the scalar
* `a` – the scalar
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `ha` – the scalar lies between the ends
* `h` – the model encloses the function

## Conclusion
* the scaled model encloses the scaled function
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product with a value of a sum of two intervals is between the sums of the two products'
stored corners: each corner of `[alo, ahi] · [r₁ + e₁, r₂ + e₂]` splits into a corner of each. -/
private theorem Taylm.aux_mul_sum_between {alo ahi r₁ r₂ e₁ e₂ : 𝕋} {y x : ℝ}
    (hy : toReal alo ≤ y ∧ y ≤ toReal ahi)
    (hx : toReal r₁ + toReal e₁ ≤ x ∧ x ≤ toReal r₂ + toReal e₂) : -- --- CONCL ---
    toReal (Interval.mulLo alo ahi r₁ r₂) + toReal (Interval.mulLo alo ahi e₁ e₂) ≤ y * x ∧
      y * x ≤ toReal (Interval.mulHi alo ahi r₁ r₂) +
        toReal (Interval.mulHi alo ahi e₁ e₂) := by -- --- PROOF ---
  -- the exact corners of the sum, then each split into the two intervals' corners
  have h := Real.Interval.mul_between_corners hy.1 hy.2 hx.1 hx.2
  have l₁ := Interval.mulLo_le alo ahi r₁ r₂
  have l₂ := Interval.mulLo_le alo ahi e₁ e₂
  have u₁ := Interval.le_mulHi alo ahi r₁ r₂
  have u₂ := Interval.le_mulHi alo ahi e₁ e₂
  simp only [Real.Interval.mulLo, Real.Interval.mulHi, mul_add] at h l₁ l₂ u₁ u₂
  constructor
  · refine le_trans (add_le_add l₁ l₂) (le_trans ?_ h.1)
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact add_le_add (min_le_of_left_le (min_le_left _ _)) (min_le_of_left_le (min_le_left _ _))
    · exact add_le_add (min_le_of_left_le (min_le_right _ _))
        (min_le_of_left_le (min_le_right _ _))
    · exact add_le_add (min_le_of_right_le (min_le_left _ _))
        (min_le_of_right_le (min_le_left _ _))
    · exact add_le_add (min_le_of_right_le (min_le_right _ _))
        (min_le_of_right_le (min_le_right _ _))
  · -- the upper end, the same with the largest corners
    refine le_trans h.2 (le_trans ?_ (add_le_add u₁ u₂))
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact add_le_add (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_left _ _))
    · exact add_le_add (le_max_of_le_left (le_max_right _ _))
        (le_max_of_le_left (le_max_right _ _))
    · exact add_le_add (le_max_of_le_right (le_max_left _ _))
        (le_max_of_le_right (le_max_left _ _))
    · exact add_le_add (le_max_of_le_right (le_max_right _ _))
        (le_max_of_le_right (le_max_right _ _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.smul_outer {alo ahi : 𝕋} {a : ℝ} (ha : toReal alo ≤ a ∧ a ≤ toReal ahi)
    {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) : -- --- CONCL ---
    (T.smul alo ahi).Encloses fun t => a * f t := by -- --- PROOF ---
  intro t ht
  have hr := h t ht
  simp only [Taylm.inflated, Real.Taylm.poly] at hr
  have hm := Taylm.aux_mul_sum_between ha hr
  -- the exact scaled coefficients against the stored upper corners
  have hround := Taylm.abs_polyOf_round_le T.terms
    (fun b => Interval.mulLo alo ahi b.1 b.1) (fun b => Interval.mulHi alo ahi b.1 b.1)
    (fun b => a * toReal b.1) (fun b => b.2)
    (fun b _ => Interval.mul_between_corners ha.1 ha.2 (le_refl _) (le_refl _)) ht
  have hex : Real.Taylm.polyOf (T.terms.map fun b => (a * toReal b.1, b.2)) t
      = a * Real.Taylm.polyOf (T.terms.map fun b => (toReal b.1, b.2)) t := by
    rw [← Real.Taylm.polyOf_smul, List.map_map]
    rfl
  rw [hex] at hround
  have := abs_le.1 hround
  have := subDown_le_sub (Interval.mulLo alo ahi T.I_error.inf T.I_error.sup)
    (listSumUp (T.terms.map fun b =>
      subUp (Interval.mulHi alo ahi b.1 b.1) (Interval.mulLo alo ahi b.1 b.1)))
  have := add_le_addUp (Interval.mulHi alo ahi T.I_error.inf T.I_error.sup)
    (listSumUp (T.terms.map fun b =>
      subUp (Interval.mulHi alo ahi b.1 b.1) (Interval.mulLo alo ahi b.1 b.1)))
  simp only [Taylm.smul, Taylm.inflated, Real.Taylm.poly, List.map_map] at *
  simp only [Function.comp_def] at *
  constructor <;> nlinarith [hm.1, hm.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
