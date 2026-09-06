import CORALean.ContSet.Ellipsoid.Real.Operations.Plus

/-!
# `Ellipsoid.plus` encloses the Minkowski sum

Given `u₁` and `u₂` in their unit balls, the point of the enclosure's ball that
reproduces `G₁u₁ + G₂u₂` is `(u₁/√(1+1/l), u₂/√(1+l))`, and its squared length
is at most `1/(1+1/l) + 1/(1+l) = l/(l+1) + 1/(l+1) = 1`. That identity is the
whole reason `Q(l)` is the family it is, and in generator form it is the only
place `l` is used.

Only `_outer`: the sum is not an ellipsoid, so no member of the family is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Ellipsoid.aux_sum_univ_plus {l : ℝ} {E₁ E₂ : Ellipsoid n}
    (f : Fin (E₁.k + E₂.k) → ℝ) :
    ∑ j : Fin (Ellipsoid.plus l E₁ E₂).k, f j
      = ∑ j, f (Fin.castAdd E₂.k j) + ∑ j, f (Fin.natAdd E₁.k j) :=
  Fin.sum_univ_add f

/-- The scalings cancel against the divisions, so the enclosure's ball point
reproduces the summands exactly. -/
theorem Ellipsoid.aux_value_plus {l : ℝ} (ha : Real.sqrt (1 + 1 / l) ≠ 0)
    (hb : Real.sqrt (1 + l) ≠ 0) (E₁ E₂ : Ellipsoid n)
    (u₁ : Vec ℝ E₁.k) (u₂ : Vec ℝ E₂.k) :
    (Ellipsoid.plus l E₁ E₂).q + (Ellipsoid.plus l E₁ E₂).G *ᵥ
        Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
          (fun j => u₂ j / Real.sqrt (1 + l))
      = (E₁.q + E₁.G *ᵥ u₁) + (E₂.q + E₂.G *ᵥ u₂) := by
  have hmul : (Ellipsoid.plus l E₁ E₂).G *ᵥ
      Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
        (fun j => u₂ j / Real.sqrt (1 + l))
      = E₁.G *ᵥ u₁ + E₂.G *ᵥ u₂ := by
    -- coordinate by coordinate, each scaling cancelling its own division
    funext i
    show ∑ j : Fin (Ellipsoid.plus l E₁ E₂).k, (Ellipsoid.plus l E₁ E₂).G i j *
        Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
          (fun j => u₂ j / Real.sqrt (1 + l)) j
      = (∑ j, E₁.G i j * u₁ j) + ∑ j, E₂.G i j * u₂ j
    rw [Ellipsoid.aux_sum_univ_plus]
    simp only [Ellipsoid.plus, Matrix.of_apply, Fin.append_left, Fin.append_right]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
      (Finset.sum_congr rfl fun j _ => ?_)
    · field_simp
    · field_simp
  show (E₁.q + E₂.q) + (Ellipsoid.plus l E₁ E₂).G *ᵥ _ = _
  rw [hmul]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

-- the enclosure holds at any positive `l`, the two scalings being read off it
theorem Ellipsoid.plus_outer (l : ℝ) (hl : 0 < l) (E₁ E₂ : Ellipsoid n) :
    E₁.construct + E₂.construct ⊆ (Ellipsoid.plus l E₁ E₂).construct := by -- --- PROOF ---
  have hlne : l ≠ 0 := ne_of_gt hl
  have hb2 : (0:ℝ) < 1 + l := by linarith
  have ha2 : (0:ℝ) < 1 + 1 / l := by -- --- PROOF ---
    have := one_div_pos.mpr hl
    linarith
  have ha : (0:ℝ) < Real.sqrt (1 + 1 / l) := Real.sqrt_pos.mpr ha2
  have hb : (0:ℝ) < Real.sqrt (1 + l) := Real.sqrt_pos.mpr hb2
  have hasq : Real.sqrt (1 + 1 / l) ^ 2 = 1 + 1 / l := Real.sq_sqrt (le_of_lt ha2)
  have hbsq : Real.sqrt (1 + l) ^ 2 = 1 + l := Real.sq_sqrt (le_of_lt hb2)
  -- each summand's ball point squared-sums to at most one
  rintro _ ⟨_, ⟨u₁, hu₁, rfl⟩, _, ⟨u₂, hu₂, rfl⟩, rfl⟩
  have hn₁ : ∑ j, u₁ j ^ 2 ≤ 1 := by
    rw [← norm₂_sq, pow_two]
    calc ‖u₁‖₂ * ‖u₁‖₂ ≤ 1 * 1 := mul_le_mul hu₁ hu₁ (norm₂_nonneg u₁) zero_le_one
      _ = 1 := one_mul 1
  have hn₂ : ∑ j, u₂ j ^ 2 ≤ 1 := by
    rw [← norm₂_sq, pow_two]
    calc ‖u₂‖₂ * ‖u₂‖₂ ≤ 1 * 1 := mul_le_mul hu₂ hu₂ (norm₂_nonneg u₂) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
    (fun j => u₂ j / Real.sqrt (1 + l)), ?_,
    (Ellipsoid.aux_value_plus (ne_of_gt ha) (ne_of_gt hb) E₁ E₂ u₁ u₂).symm⟩
  -- the appended coefficient's squared sum, one block at a time
  have hsum : ∑ j : Fin (Ellipsoid.plus l E₁ E₂).k,
      Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
        (fun j => u₂ j / Real.sqrt (1 + l)) j ^ 2 ≤ 1 := by
    rw [Ellipsoid.aux_sum_univ_plus]
    simp only [Fin.append_left, Fin.append_right]
    have hd₁ : ∑ j, (u₁ j / Real.sqrt (1 + 1 / l)) ^ 2
        = (∑ j, u₁ j ^ 2) * (Real.sqrt (1 + 1 / l) ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]
    have hd₂ : ∑ j, (u₂ j / Real.sqrt (1 + l)) ^ 2
        = (∑ j, u₂ j ^ 2) * (Real.sqrt (1 + l) ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]
    rw [hd₁, hd₂, hasq, hbsq]
    -- and `(1+1/l)⁻¹ + (1+l)⁻¹ = 1` is what makes the two blocks fit the unit ball
    calc (∑ j, u₁ j ^ 2) * (1 + 1 / l)⁻¹ + (∑ j, u₂ j ^ 2) * (1 + l)⁻¹
        ≤ 1 * (1 + 1 / l)⁻¹ + 1 * (1 + l)⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right hn₁ (le_of_lt (inv_pos.mpr ha2)))
            (mul_le_mul_of_nonneg_right hn₂ (le_of_lt (inv_pos.mpr hb2)))
      _ = 1 := by
          rw [one_mul, one_mul]
          field_simp
          ring
  calc ‖Fin.append (fun j => u₁ j / Real.sqrt (1 + 1 / l))
        (fun j => u₂ j / Real.sqrt (1 + l))‖₂
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
    _ = 1 := Real.sqrt_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
