import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

/-!
# A box as an ellipsoid, over a floating-point scalar

The smallest ellipsoid containing a box is `√n` times the inscribed one, so this
is the second place the layer meets a square root — and it is answered the same
way: the caller proposes `σ` and `n ≤ σ·σ` is checked. Nothing else about `σ`
is used, so the classical `√n` is the tightest admissible value rather than a
required one.

Directly rather than through the zonotope, which is the route over ℝ. The
zonotope step would contribute nothing here: a box's generators are already
`diag(radiusFrom)`, and going through them would only re-derive the coefficients
this proof reads off the box.

The generators round *up*, and that is what lets the error box stay empty. A
coordinate's coefficient is `(xᵢ - cᵢ)/gᵢ`, which an upward-rounded `gᵢ` only
makes smaller — so the ball point stays inside the ball and the enclosure is
exact in the arithmetic, not merely paid for. Rounding down would have cost a
box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- One generator per coordinate, the box's own radius scaled by the proposed
`√n` and rounded up. -/
def Interval.ellipsoidG (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n n :=
  diagonalBlock fun i => mulUp σ (I.radiusFrom i)

def Interval.ellipsoid (I : Interval (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  k := n
  q := I.center
  G := I.ellipsoidG σ
  err := ⟨fun _ => zero, fun _ => zero⟩

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored generator covers the exact scaling, so no coordinate's
coefficient exceeds `1/σ`. -/
theorem Interval.aux_ellipsoidG_ge (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (i : Fin n) :
    toReal σ * toReal (I.radiusFrom i) ≤ toReal (I.ellipsoidG σ i i) := by
  show _ ≤ toReal (diagonalBlock (fun i => mulUp σ (I.radiusFrom i)) i i)
  rw [diagonalBlock, if_pos rfl]
  exact mul_le_mulUp _ _

theorem Interval.subset_nominal_ellipsoid (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) :
    I.construct ⊆ nominalSet (I.ellipsoid σ) := by -- --- PROOF ---
  intro x hx
  have hreach : ∀ i, toReal (I.center i) - toReal (I.radiusFrom i) ≤ x i
      ∧ x i ≤ toReal (I.center i) + toReal (I.radiusFrom i) := fun i =>
    ⟨le_trans (I.reaches i).1 (hx i).1, le_trans (hx i).2 (I.reaches i).2⟩
  have hrad : ∀ i, 0 ≤ toReal (I.radiusFrom i) := fun i => by
    have h₁ := (hreach i).1
    have h₂ := (hreach i).2
    linarith
  have hg : ∀ i, 0 ≤ toReal (I.ellipsoidG σ i i) := fun i =>
    le_trans (mul_nonneg (le_of_lt hσ) (hrad i)) (I.aux_ellipsoidG_ge σ i)
  -- a coordinate the generator cannot reach is one the box did not move
  have hzero : ∀ i, toReal (I.ellipsoidG σ i i) = 0 → x i = toReal (I.center i) := by
    intro i h
    have hle := I.aux_ellipsoidG_ge σ i
    rw [h] at hle
    have hr : toReal (I.radiusFrom i) ≤ 0 := nonpos_of_mul_nonpos_right hle hσ
    have h₁ := (hreach i).1
    have h₂ := (hreach i).2
    have hr0 : toReal (I.radiusFrom i) = 0 := le_antisymm hr (hrad i)
    rw [hr0] at h₁ h₂
    linarith
  -- the coefficient a coordinate needs, zero where the generator has no width
  set u : Vec ℝ n := fun i => if toReal (I.ellipsoidG σ i i) = 0 then 0
    else (x i - toReal (I.center i)) / toReal (I.ellipsoidG σ i i) with hudef
  have hne : toReal σ ≠ 0 := ne_of_gt hσ
  have hub : ∀ i, |u i| ≤ 1 / toReal σ := by
    intro i
    have hkey : toReal σ * |u i| ≤ 1 := by
      by_cases h : toReal (I.ellipsoidG σ i i) = 0
      · rw [hudef]
        simp only [if_pos h, abs_zero, mul_zero]
        exact zero_le_one
      -- otherwise the division is legal, and `aux_ellipsoidG_ge` is what bounds it
      · have hpos : 0 < toReal (I.ellipsoidG σ i i) := lt_of_le_of_ne (hg i) (Ne.symm h)
        have habs : |x i - toReal (I.center i)| ≤ toReal (I.radiusFrom i) := by
          rw [abs_le]
          exact ⟨by linarith [(hreach i).1], by linarith [(hreach i).2]⟩
        rw [hudef]
        simp only [if_neg h, abs_div, abs_of_pos hpos]
        rw [← mul_div_assoc, div_le_one hpos]
        calc toReal σ * |x i - toReal (I.center i)|
            ≤ toReal σ * toReal (I.radiusFrom i) :=
              mul_le_mul_of_nonneg_left habs (le_of_lt hσ)
          _ ≤ toReal (I.ellipsoidG σ i i) := I.aux_ellipsoidG_ge σ i
    have hinv : (0:ℝ) < 1 / toReal σ := one_div_pos.mpr hσ
    calc |u i| = (1 / toReal σ) * (toReal σ * |u i|) := by field_simp
      _ ≤ (1 / toReal σ) * 1 := mul_le_mul_of_nonneg_left hkey (le_of_lt hinv)
      _ = 1 / toReal σ := mul_one _
  -- `n` coordinates each within `1/σ` keep the Euclidean norm inside the unit ball
  have hnorm : ‖u‖₂ ≤ 1 := by
    have hσ2 : (0:ℝ) < toReal σ ^ 2 := by
      rw [pow_two]
      exact mul_pos hσ hσ
    have hnle : (n : ℝ) ≤ toReal σ ^ 2 := by
      rw [pow_two]
      exact le_trans hn (mulDown_le_mul σ σ)
    have hsum : ∑ i, u i ^ 2 ≤ 1 := by
      have hterm : ∀ i : Fin n, u i ^ 2 ≤ (1 / toReal σ) * (1 / toReal σ) := by
        intro i
        rw [← sq_abs, pow_two]
        exact mul_le_mul (hub i) (hub i) (abs_nonneg _) (le_of_lt (one_div_pos.mpr hσ))
      -- summing the `n` equal bounds, which is what `hn` says `σ²` covers
      refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
      have hconst : (∑ _i : Fin n, (1 / toReal σ) * (1 / toReal σ))
          = (n : ℝ) * ((1 / toReal σ) * (1 / toReal σ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hprod : (1 / toReal σ) * (1 / toReal σ) = 1 / toReal σ ^ 2 := by
        rw [pow_two]
        field_simp
      rw [hconst, hprod, mul_one_div, div_le_one hσ2]
      exact hnle
    calc ‖u‖₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  refine Ellipsoid.mem_nominalSet_iff.mpr ⟨u, hnorm, fun i => ?_⟩
  -- only the diagonal entry survives, and it cancels against its own division
  have hdiag : (∑ j, toReal ((I.ellipsoid σ).G i j) * u j)
      = toReal (I.ellipsoidG σ i i) * u i :=
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj => by
      have hij : ¬ (i = j) := fun h => hj h.symm
      show toReal (diagonalBlock (fun i => mulUp σ (I.radiusFrom i)) i j) * u j = 0
      rw [diagonalBlock, if_neg hij, toReal_zero, zero_mul]
  show x i = toReal (I.center i) + ∑ j, toReal ((I.ellipsoid σ).G i j) * u j
  rw [hdiag]
  -- a zero-width coordinate is the centre; otherwise the division cancels
  by_cases h : toReal (I.ellipsoidG σ i i) = 0
  · rw [hudef]
    simp only [if_pos h]
    rw [mul_zero, add_zero]
    exact hzero i h
  · rw [hudef]
    simp only [if_neg h]
    rw [mul_comm (toReal (I.ellipsoidG σ i i))
      ((x i - toReal (I.center i)) / toReal (I.ellipsoidG σ i i)),
      div_mul_cancel₀ _ h]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ellipsoid_contains (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) :
    I.construct ⊆ (I.ellipsoid σ).construct := fun x hx =>
  ⟨x, I.subset_nominal_ellipsoid σ hσ hn hx, 0, fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩, by show x + 0 = x; rw [add_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
