module

public import CORALean.Global.Float.SinCos

@[expose] public section

/-!
# The tangent rounded in either direction

`tan x = sin x / cos x`, the sine bound over the two bounds on the cosine. The quotient is only
bounded where the cosine is certified positive, so both carry the hypothesis
`0 < toReal (cosDown n x)`, which a caller discharges by evaluating `cosDown` (`ltStrict` against
`zero` certifies it), as `le_expUp_of_le` discharges `expUp`'s range. No fallback is possible:
the tangent is unbounded.

## Inputs
* `n` – number of halvings
* `x` – float argument

## Hypotheses
* `hc` – the downward cosine bound is positive

## Conclusion
* the downward tangent bound is at most the tangent
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-- `tan x` from below, where `cosDown n x` is positive. -/
def tanDown (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let sl := sinDown n x
  minimum (divDown sl cl) (divDown sl cu)

/-- `tan x` from above, where `cosDown n x` is positive. -/
def tanUp (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let su := sinUp n x
  maximum (divUp su cl) (divUp su cu)

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- `s / c` between `s` over the two bounds on a positive `c`. -/
private theorem div_between (s : ℝ) {c cl cu : ℝ} (hl : 0 < cl) (h1 : cl ≤ c)
    (h2 : c ≤ cu) : -- --- CONCL ---
    min (s / cl) (s / cu) ≤ s / c ∧ s / c ≤ max (s / cl) (s / cu) := by -- --- PROOF ---
  have hc : 0 < c := lt_of_lt_of_le hl h1
  have i1 : c⁻¹ ≤ cl⁻¹ := inv_anti₀ hl h1
  have i2 : cu⁻¹ ≤ c⁻¹ := inv_anti₀ hc h2
  simp only [div_eq_mul_inv]
  rcases le_total 0 s with hs | hs
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonneg_left i2 hs),
      le_max_of_le_left (mul_le_mul_of_nonneg_left i1 hs)⟩
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonpos_left i1 hs),
      le_max_of_le_right (mul_le_mul_of_nonpos_left i2 hs)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanDown_le (n : ℕ) (x : 𝕋) (hc : 0 < toReal (cosDown n x)) : -- --- CONCL ---
    toReal (tanDown n x) ≤ Real.tan (toReal x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcu : 0 < toReal (cosUp n x) := by linarith
  have hcx : 0 < Real.cos (toReal x) := by linarith
  have hb := div_between (toReal (sinDown n x)) hc h1 h2
  rw [Real.tan_eq_sin_div_cos]
  refine le_trans ?_ (le_trans hb.1 (div_le_div_of_nonneg_right (sinDown_le n x) hcx.le))
  simp only [tanDown, toReal_minimum]
  exact min_le_min (divDown_le_div _ _ hc) (divDown_le_div _ _ hcu)

/-- `tanUp` is an upper bound of `tan` where `cosDown` is positive. -/
theorem le_tanUp (n : ℕ) (x : 𝕋) (hc : 0 < toReal (cosDown n x)) : -- --- CONCL ---
    Real.tan (toReal x) ≤ toReal (tanUp n x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcu : 0 < toReal (cosUp n x) := by linarith
  have hcx : 0 < Real.cos (toReal x) := by linarith
  have hb := div_between (toReal (sinUp n x)) hc h1 h2
  rw [Real.tan_eq_sin_div_cos]
  refine le_trans (le_trans (div_le_div_of_nonneg_right (le_sinUp n x) hcx.le) hb.2) ?_
  simp only [tanUp, toReal_maximum]
  exact max_le_max (div_le_divUp _ _ hc) (div_le_divUp _ _ hcu)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
