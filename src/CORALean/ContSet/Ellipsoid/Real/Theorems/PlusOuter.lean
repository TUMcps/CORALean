module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus

@[expose] public section

/-!
# `Ellipsoid.plus` encloses the Minkowski sum

Given `u₁` and `u₂` in their unit balls, the point of the enclosure's ball that
reproduces `G₁u₁ + G₂u₂` is `(u₁/s₁, u₂/s₂)`, whose squared length is at most
`1/s₁² + 1/s₂²` — which is exactly the hypothesis. Nothing else about the pair
is used, so soundness holds at every admissible pair and which one a caller
picks is a precision choice owing no proof, the way `ConPolyZono.reduceBy_outer`
holds at every partition and `Relaxation.ofDeriv` at every slope in its bracket.

Kurzhanski and Varaiya's `l` sweeps the boundary, where the bound is met with
equality; `plus_scalings_admissible` discharges all three hypotheses from it.

Division appears in that ball point and only there. The scalings are non-zero
because the hypothesis gives their reciprocals a finite sum, so the caller
states that separately — `1/0` is `0` in Lean and would otherwise satisfy the
bound vacuously, at a `plus` whose generators are all zero.

Only `_outer`: the sum is not an ellipsoid, so no member of the family is exact.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Ellipsoid.aux_sum_univ_plus {s₁ s₂ : ℝ} {E₁ E₂ : Ellipsoid n}
    (f : Fin (E₁.k + E₂.k) → ℝ) :
    ∑ j : Fin (Ellipsoid.plus s₁ s₂ E₁ E₂).k, f j
      = ∑ j, f (Fin.castAdd E₂.k j) + ∑ j, f (Fin.natAdd E₁.k j) :=
  Fin.sum_univ_add f

/-- The scalings cancel against the divisions, so the enclosure's ball point
reproduces the summands exactly. -/
theorem Ellipsoid.aux_value_plus {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0) (hne₂ : s₂ ≠ 0)
    (E₁ E₂ : Ellipsoid n) (u₁ : Vec ℝ E₁.k) (u₂ : Vec ℝ E₂.k) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).c + (Ellipsoid.plus s₁ s₂ E₁ E₂).G *ᵥ
        Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂)
      = (E₁.c + E₁.G *ᵥ u₁) + (E₂.c + E₂.G *ᵥ u₂) := by -- --- PROOF ---
  have hmul : (Ellipsoid.plus s₁ s₂ E₁ E₂).G *ᵥ
      Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂)
      = E₁.G *ᵥ u₁ + E₂.G *ᵥ u₂ := by
    -- coordinate by coordinate, each scaling cancelling its own division
    funext i
    show ∑ j : Fin (Ellipsoid.plus s₁ s₂ E₁ E₂).k, (Ellipsoid.plus s₁ s₂ E₁ E₂).G i j *
        Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂) j
      = (∑ j, E₁.G i j * u₁ j) + ∑ j, E₂.G i j * u₂ j
    rw [Ellipsoid.aux_sum_univ_plus]
    simp only [Ellipsoid.plus, Matrix.of_apply, Fin.append_left, Fin.append_right]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
      (Finset.sum_congr rfl fun j _ => ?_)
    · field_simp
    · field_simp
  show (E₁.c + E₂.c) + (Ellipsoid.plus s₁ s₂ E₁ E₂).G *ᵥ _ = _
  rw [hmul]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

-- the enclosure holds at every admissible pair, the inequality being all that is used
theorem Ellipsoid.plus_outer (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) (hne₁ : s₁ ≠ 0)
    (hne₂ : s₂ ≠ 0) (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) :
    E₁.construct + E₂.construct ⊆ (Ellipsoid.plus s₁ s₂ E₁ E₂).construct := by -- --- PROOF ---
  have hsq₁ : (0:ℝ) < s₁ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₁))
  have hsq₂ : (0:ℝ) < s₂ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₂))
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
  refine ⟨Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂), ?_,
    (Ellipsoid.aux_value_plus hne₁ hne₂ E₁ E₂ u₁ u₂).symm⟩
  -- the appended coefficient's squared sum, one block at a time
  have hsum : ∑ j : Fin (Ellipsoid.plus s₁ s₂ E₁ E₂).k,
      Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂) j ^ 2 ≤ 1 := by
    rw [Ellipsoid.aux_sum_univ_plus]
    simp only [Fin.append_left, Fin.append_right]
    have hd₁ : ∑ j, (u₁ j / s₁) ^ 2 = (∑ j, u₁ j ^ 2) * (s₁ ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]
    have hd₂ : ∑ j, (u₂ j / s₂) ^ 2 = (∑ j, u₂ j ^ 2) * (s₂ ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]
    have hinv : (s₁ ^ 2)⁻¹ + (s₂ ^ 2)⁻¹ ≤ 1 := by
      rw [← one_div, ← one_div]
      exact hs
    rw [hd₁, hd₂]
    -- and the hypothesis is what makes the two blocks fit inside the unit ball
    calc (∑ j, u₁ j ^ 2) * (s₁ ^ 2)⁻¹ + (∑ j, u₂ j ^ 2) * (s₂ ^ 2)⁻¹
        ≤ 1 * (s₁ ^ 2)⁻¹ + 1 * (s₂ ^ 2)⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right hn₁ (le_of_lt (inv_pos.mpr hsq₁)))
            (mul_le_mul_of_nonneg_right hn₂ (le_of_lt (inv_pos.mpr hsq₂)))
      _ ≤ 1 := by
          rw [one_mul, one_mul]
          exact hinv
  calc ‖Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂)‖₂
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
    _ = 1 := Real.sqrt_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
