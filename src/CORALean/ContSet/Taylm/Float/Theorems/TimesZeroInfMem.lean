module

public import CORALean.ContSet.Taylm.Float.Operations.TimesZeroInf
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Taylm.timesZeroInf` holds the products

## Inputs
* `a` – first factor
* `b` – second factor
* `x` – point of the first factor
* `y` – point of the second factor

## Hypotheses
* `hx₁` – `x` is above the lower end of `a`
* `hx₂` – `x` is below the upper end of `a`
* `hy₁` – `y` is above the lower end of `b`
* `hy₂` – `y` is below the upper end of `b`

## Conclusion
* `x * y` lies in the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float that compares equal to zero both ways is zero. -/
private theorem Taylm.aux_toReal_eq_zero {u : 𝕋}
    (h : (le u zero && le zero u) = true) : -- --- CONCL ---
    toReal u = 0 := by -- --- PROOF ---
  simp only [Bool.and_eq_true] at h
  have h₁ := toReal_le_of_le h.1
  have h₂ := toReal_le_of_le h.2
  rw [toReal_zero] at h₁ h₂
  linarith

/-- A lower corner is at most the product, the zero corner included. -/
private theorem Taylm.aux_lo_le (u v : 𝕋) :
    toReal (if (le u zero && le zero u) || (le v zero && le zero v) then zero else mulDown u v)
      ≤ toReal u * toReal v := by
  split_ifs with h
  · rcases Bool.or_eq_true_iff.1 h with h | h <;> simp [Taylm.aux_toReal_eq_zero h, toReal_zero]
  · exact mulDown_le_mul u v

/-- An upper corner is at least the product, the zero corner included. -/
private theorem Taylm.aux_le_hi (u v : 𝕋) :
    toReal u * toReal v ≤ toReal (if (le u zero && le zero u) || (le v zero && le zero v)
      then zero else mulUp u v) := by
  split_ifs with h
  · rcases Bool.or_eq_true_iff.1 h with h | h <;> simp [Taylm.aux_toReal_eq_zero h, toReal_zero]
  · exact mul_le_mulUp u v


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.timesZeroInf_mem {a b : Interval 𝕋} {x y : ℝ} (hx₁ : toReal a.inf ≤ x)
    (hx₂ : x ≤ toReal a.sup) (hy₁ : toReal b.inf ≤ y) (hy₂ : y ≤ toReal b.sup) : -- --- CONCL ---
    toReal (Taylm.timesZeroInf a b).inf ≤ x * y ∧
      x * y ≤ toReal (Taylm.timesZeroInf a b).sup := by -- --- PROOF ---
  have hc := Real.Interval.mul_between_corners hx₁ hx₂ hy₁ hy₂
  simp only [Real.Interval.mulLo, Real.Interval.mulHi] at hc
  have l₁ := Taylm.aux_lo_le a.inf b.inf
  have l₂ := Taylm.aux_lo_le a.inf b.sup
  have l₃ := Taylm.aux_lo_le a.sup b.inf
  have l₄ := Taylm.aux_lo_le a.sup b.sup
  have u₁ := Taylm.aux_le_hi a.inf b.inf
  have u₂ := Taylm.aux_le_hi a.inf b.sup
  have u₃ := Taylm.aux_le_hi a.sup b.inf
  have u₄ := Taylm.aux_le_hi a.sup b.sup
  simp only [Taylm.timesZeroInf, toReal_minimum, toReal_maximum]
  -- the hull of the float corners is outside the hull of the real ones
  constructor
  · refine le_trans ?_ hc.1
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) l₁))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) l₂))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) l₃)
    · exact le_trans (min_le_right _ _) l₄
  · refine le_trans hc.2 ?_
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact le_trans u₁
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    · exact le_trans u₂
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    · exact le_trans u₃ (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans u₄ (le_max_left _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
