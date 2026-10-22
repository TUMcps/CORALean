module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Ellipsoid
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalReaches
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor

@[expose] public section

/-!
# A box as an ellipsoid, over a floating-point scalar

The smallest ellipsoid containing a box is `√n` times the inscribed one, so this is a place the
layer meets a square root, answered as elsewhere: the caller proposes `σ` and `n ≤ σ·σ` is checked,
so the classical `√n` is the tightest admissible value rather than a required one. Directly rather
than through the zonotope: a box's generators are already `diag(radiusFrom)`. The generators round
*up*, which lets the error box stay empty: a coordinate's coefficient is `(xᵢ - cᵢ)/gᵢ`, which an
upward-rounded `gᵢ` only makes smaller, so the enclosure is exact in the arithmetic, not merely paid
for. Rounding down would have cost a box.

## Inputs
* `I` – interval
* `σ` – scaling factor

## Hypotheses
* `hσ` – scaling factor positive
* `hn` – squared scaling factor at least dimension

## Conclusion
* interval is contained in its ellipsoid
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix

/-- The stored generator covers the exact scaling, so no coordinate's
coefficient exceeds `1/σ`. -/
theorem Interval.aux_ellipsoidG_ge (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (i : Fin n) :
    toReal σ * toReal (I.radiusFrom i) ≤ toReal (I.ellipsoidG σ i i) := by
  show _ ≤ toReal (diagonalBlock (fun i => mulUp σ (I.radiusFrom i)) i i)
  rw [diagonalBlock, if_pos rfl]
  exact mul_le_mulUp _ _


/-- A box lies in its nominal ellipsoid. -/
theorem Interval.aux_subset_nominal_ellipsoid (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) : -- --- CONCL ---
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
  -- `x = c + diag(g) u`, a point of the ellipsoid generated by `diag(g)`
  set Gr : Mat ℝ n n := toRealMat (I.ellipsoidG σ) with hGr
  have hx' : x = toRealVec I.center + Gr *ᵥ u := by
    funext i
    -- only the diagonal entry survives, and it cancels against its own division
    have hdiag : (Gr *ᵥ u) i = toReal (I.ellipsoidG σ i i) * u i :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj => by
        have hij : ¬ (i = j) := fun h => hj h.symm
        show toReal (diagonalBlock (fun i => mulUp σ (I.radiusFrom i)) i j) * u j = 0
        rw [diagonalBlock, if_neg hij, toReal_zero, zero_mul]
    show x i = toReal (I.center i) + (Gr *ᵥ u) i
    rw [hdiag]
    -- a zero-width coordinate is the center; otherwise the division cancels
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
  set F := Real.Ellipsoid.ofFactor Gr (toRealVec I.center) with hF
  have hxF : x ∈ F.construct := by
    rw [hF, Real.Ellipsoid.construct_ofFactor]
    exact ⟨u, hnorm, hx'⟩
  -- the stored diagonal dominates `diag(g)²`
  have hdom : (toRealMat (I.ellipsoid σ).Q - F.Q).PosSemidef := by
    have heq : toRealMat (I.ellipsoid σ).Q - F.Q = Matrix.diagonal fun i =>
        toReal (mulUp (I.ellipsoidG σ i i) (I.ellipsoidG σ i i))
          - toReal (I.ellipsoidG σ i i) * toReal (I.ellipsoidG σ i i) := by
      ext i j
      show toReal (diagonalBlock (𝕋 := 𝕋)
        (fun i => mulUp (I.ellipsoidG σ i i) (I.ellipsoidG σ i i)) i j) - (Gr * Grᵀ) i j = _
      rw [toReal_diagonalBlock, hGr]
      by_cases hij : i = j
      · -- on the diagonal, `Gr Grᵀ` is the one square `gᵢ²`
        subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.transpose_apply, toRealMat]
        rw [Finset.sum_eq_single i (fun l _ hl => by
          show toReal (diagonalBlock (𝕋 := 𝕋) (fun i => mulUp σ (I.radiusFrom i)) i l)
            * toReal (diagonalBlock (𝕋 := 𝕋) (fun i => mulUp σ (I.radiusFrom i)) i l) = 0
          rw [diagonalBlock, if_neg (Ne.symm hl), toReal_zero, zero_mul]) (by simp)]
        rfl
      · -- off it, every product has a zero factor
        simp only [Matrix.diagonal_apply_ne _ hij, Matrix.mul_apply, Matrix.transpose_apply,
          toRealMat, sub_eq_zero]
        refine (Finset.sum_eq_zero fun l _ => ?_).symm
        show toReal (diagonalBlock (𝕋 := 𝕋) (fun i => mulUp σ (I.radiusFrom i)) i l)
          * toReal (diagonalBlock (𝕋 := 𝕋) (fun i => mulUp σ (I.radiusFrom i)) j l) = 0
        by_cases hil : i = l
        · subst hil
          rw [diagonalBlock, diagonalBlock, if_neg (Ne.symm hij), toReal_zero, mul_zero]
        · rw [diagonalBlock, if_neg hil, toReal_zero, zero_mul]
    rw [heq]
    exact Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (mul_le_mulUp _ _)
  have hmem := Ellipsoid.add_sub_mem_nominalSet (Or.inr hdom) hxF
  have hq : toRealVec (I.ellipsoid σ).q = F.q := rfl
  rwa [hq, add_sub_cancel] at hmem

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ellipsoid_contains (I : Interval (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) :
    I.construct ⊆ (I.ellipsoid σ).construct := fun x hx =>
  ⟨x, I.aux_subset_nominal_ellipsoid σ hσ hn hx, 0, fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩, by show x + 0 = x; rw [add_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
