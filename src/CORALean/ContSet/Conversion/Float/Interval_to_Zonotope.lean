import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# A box as a zonotope, over a floating-point scalar

The centre may be rounded any way at all — the radius is then measured *from the
centre that was actually stored*, upward on both sides, so it reaches whichever
end the rounding moved away from. That is why the radius is a maximum of two
directed differences rather than half the width: half a rounded width would
leave one edge short whenever the centre moved.

Nothing goes into the error box. The generators already cover the rounding, and
paying for it twice would only widen the result.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Any point of the box would do; the midpoint keeps the generators small. -/
def Interval.center (I : Interval 𝕋 n) : Vec 𝕋 n := fun i => half (addUp (I.inf i) (I.sup i))

/-- Far enough from the stored centre to reach both ends. -/
def Interval.radiusFrom (I : Interval 𝕋 n) : Vec 𝕋 n :=
  fun i => maximum (subUp (I.sup i) (I.center i)) (subUp (I.center i) (I.inf i))

theorem Interval.reaches (I : Interval 𝕋 n) (i : Fin n) :
    toReal (I.center i) - toReal (I.radiusFrom i) ≤ toReal (I.inf i)
      ∧ toReal (I.sup i) ≤ toReal (I.center i) + toReal (I.radiusFrom i) := by
  have hhi := sub_le_subUp (I.sup i) (I.center i)
  have hlo := sub_le_subUp (I.center i) (I.inf i)
  rw [Interval.radiusFrom, toReal_maximum]
  constructor
  · have h : toReal (I.center i) - toReal (I.inf i) ≤ max
        (toReal (subUp (I.sup i) (I.center i))) (toReal (subUp (I.center i) (I.inf i))) :=
      le_trans hlo (le_max_right _ _)
    linarith
  · have h : toReal (I.sup i) - toReal (I.center i) ≤ max
        (toReal (subUp (I.sup i) (I.center i))) (toReal (subUp (I.center i) (I.inf i))) :=
      le_trans hhi (le_max_left _ _)
    linarith

-- the stored centre, and one diagonal generator per coordinate
def Interval.zonotope (I : Interval 𝕋 n) : Zonotope 𝕋 n where
  h := n
  c := I.center
  G := diagonalBlock I.radiusFrom
  E := ⟨fun _ => zero, fun _ => zero⟩

/-- The generators alone already cover the box, before the error box is even
consulted — which is what lets a caller read off coefficients directly. -/
theorem Interval.subset_nominal_zonotope (I : Interval 𝕋 n) :
    I.construct ⊆ InflatedContSet.nominalSet I.zonotope := by -- --- PROOF ---
  intro x hx
  have hlo : ∀ i, toReal (I.inf i) ≤ x i := fun i => (hx i).1
  have hhi : ∀ i, x i ≤ toReal (I.sup i) := fun i => (hx i).2
  have hreach : ∀ i, toReal (I.center i) - toReal (I.radiusFrom i) ≤ x i
      ∧ x i ≤ toReal (I.center i) + toReal (I.radiusFrom i) := fun i =>
    ⟨le_trans (I.reaches i).1 (hlo i), le_trans (hhi i) (I.reaches i).2⟩
  -- the coefficient a coordinate needs, zero where the box has no width there
  refine ⟨fun i => if toReal (I.radiusFrom i) = 0 then 0
      else (x i - toReal (I.center i)) / toReal (I.radiusFrom i), fun i => ?_, ?_⟩
  · by_cases h : toReal (I.radiusFrom i) = 0
    · simp only [if_pos h, abs_zero]
      norm_num
    · have hpos : 0 < toReal (I.radiusFrom i) :=
        lt_of_le_of_ne (by linarith [(hreach i).1, (hreach i).2]) (Ne.symm h)
      simp only [if_neg h]
      rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
      constructor <;> linarith [(hreach i).1, (hreach i).2]
  -- the value: only the diagonal entry `i` reaches coordinate `i`
  · funext i
    have hsum : (∑ j : Fin n, (if toReal (I.radiusFrom j) = 0 then (0:ℝ)
          else (x j - toReal (I.center j)) / toReal (I.radiusFrom j)) •
            (fun i => toReal (diagonalBlock I.radiusFrom i j) : Vec ℝ n)) i
        = (if toReal (I.radiusFrom i) = 0 then (0:ℝ)
            else (x i - toReal (I.center i)) / toReal (I.radiusFrom i))
          * toReal (I.radiusFrom i) := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [toReal_diagonalBlock, Matrix.diagonal_apply_eq, toRealVec]
      · intro j _ hj
        have hij : i ≠ j := Ne.symm hj
        simp [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ hij]
      · intro hc
        exact absurd (Finset.mem_univ i) hc
    -- the goal spelled out, so `hsum` matches it
    show x i = ((fun i => toReal (I.center i) : Vec ℝ n)
      + ∑ j : Fin n, (if toReal (I.radiusFrom j) = 0 then (0:ℝ)
        else (x j - toReal (I.center j)) / toReal (I.radiusFrom j)) •
          (fun i => toReal (diagonalBlock I.radiusFrom i j) : Vec ℝ n)) i
    rw [Pi.add_apply, hsum]
    by_cases h : toReal (I.radiusFrom i) = 0
    · rw [if_pos h, zero_mul, add_zero]
      have h₁ := (hreach i).1
      have h₂ := (hreach i).2
      rw [h] at h₁ h₂
      linarith
    · rw [if_neg h, div_mul_cancel₀ _ h]
      ring


-- =======================================  MAIN THEOREM  ======================================= --

-- the error box adds nothing, the generators already covering the box
theorem Interval.subset_zonotope (I : Interval 𝕋 n) :
    I.construct ⊆ I.zonotope.construct := fun x hx =>
  ⟨x, I.subset_nominal_zonotope hx, 0, fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩, by show x + 0 = x; rw [add_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
