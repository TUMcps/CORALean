module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqOfFactor

@[expose] public section

/-!
# `Ellipsoid.plus` encloses the Minkowski sum

The shape `s₁² Q₁ + s₂² Q₂` is `H Hᵀ` for `H = [s₁ G₁ | s₂ G₂]`, so the enclosure is the image of
the unit ball of `ℝ²ⁿ` under `H` (`construct_eq_of_factor`). Given `u₁` and `u₂` in their unit
balls, the point of that ball reproducing `G₁u₁ + G₂u₂` is `(u₁/s₁, u₂/s₂)`, of squared length at
most `1/s₁² + 1/s₂²`, exactly the hypothesis. Soundness holds at every admissible pair and which one
a caller picks is a precision choice (Kurzhanski and Varaiya's `l` meets the bound with equality,
`plus_scalings_admissible`). The scalings are non-zero by a separate hypothesis: `1/0` is `0` in
Lean and would satisfy the bound vacuously. Only `_outer`: the sum is not an ellipsoid.

## Inputs
* `s₁` – scaling of `E₁`
* `s₂` – scaling of `E₂`
* `E₁` – first ellipsoid
* `E₂` – second ellipsoid

## Hypotheses
* `hne₁` – `s₁ ≠ 0`
* `hne₂` – `s₂ ≠ 0`
* `hs` – `1/s₁² + 1/s₂² ≤ 1`

## Conclusion
* the Minkowski sum lies in the result
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The two scaled square roots side by side, a factor of `plus`'s shape matrix. -/
private noncomputable def aux_H (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) : Mat ℝ n (n + n) :=
  Matrix.of fun i => Fin.append (fun j => s₁ * E₁.G i j) (fun j => s₂ * E₂.G i j)

/-- `H Hᵀ = s₁² G₁ G₁ᵀ + s₂² G₂ G₂ᵀ`, block by block. -/
private theorem aux_H_mul_transpose (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) :
    aux_H s₁ s₂ E₁ E₂ * (aux_H s₁ s₂ E₁ E₂)ᵀ = (Ellipsoid.plus s₁ s₂ E₁ E₂).Q := by -- --- PROOF ---
  show _ = s₁ ^ 2 • E₁.Q + s₂ ^ 2 • E₂.Q
  rw [← E₁.G_mul_transpose, ← E₂.G_mul_transpose]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, aux_H, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring

/-- The scalings cancel against the divisions, so the enclosure's ball point
reproduces the summands exactly. -/
private theorem aux_value_plus {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0) (hne₂ : s₂ ≠ 0)
    (E₁ E₂ : Ellipsoid n) (u₁ u₂ : Vec ℝ n) :
    (E₁.q + E₂.q) + aux_H s₁ s₂ E₁ E₂ *ᵥ Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂)
      = (E₁.q + E₁.G *ᵥ u₁) + (E₂.q + E₂.G *ᵥ u₂) := by -- --- PROOF ---
  have hmul : aux_H s₁ s₂ E₁ E₂ *ᵥ Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂)
      = E₁.G *ᵥ u₁ + E₂.G *ᵥ u₂ := by
    -- coordinate by coordinate, each scaling cancelling its own division
    funext i
    simp only [Matrix.mulVec, dotProduct, aux_H, Matrix.of_apply, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right, Pi.add_apply]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
      (Finset.sum_congr rfl fun j _ => ?_)
    · field_simp
    · field_simp
  rw [hmul]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

-- the enclosure holds at every admissible pair, the inequality being all that is used
theorem Ellipsoid.plus_outer (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) (hne₁ : s₁ ≠ 0)
    (hne₂ : s₂ ≠ 0) (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) :
    E₁.construct + E₂.construct ⊆ (Ellipsoid.plus s₁ s₂ E₁ E₂).construct := by -- --- PROOF ---
  rw [E₁.construct_eq_sqrt, E₂.construct_eq_sqrt]
  have hsq₁ : (0:ℝ) < s₁ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₁))
  have hsq₂ : (0:ℝ) < s₂ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₂))
  -- each summand's ball point squared-sums to at most one
  rw [(Ellipsoid.plus s₁ s₂ E₁ E₂).construct_eq_of_factor _ (aux_H_mul_transpose s₁ s₂ E₁ E₂)]
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
    (aux_value_plus hne₁ hne₂ E₁ E₂ u₁ u₂).symm⟩
  -- the appended coefficient's squared sum, one block at a time
  have hsum : ∑ j : Fin (n + n),
      Fin.append (fun j => u₁ j / s₁) (fun j => u₂ j / s₂) j ^ 2 ≤ 1 := by
    rw [Fin.sum_univ_add]
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
