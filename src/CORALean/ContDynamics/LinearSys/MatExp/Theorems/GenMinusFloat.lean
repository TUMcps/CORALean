import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinusFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The float `G^{(-)}_h` holds the true generators' magnitudes

For a matrix `E = e^{AΔt}` that `[e^{AΔt}]` holds, every entry of `(E - I_n) G_l` is under the
float entry in magnitude.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real between two floats is under the larger of their magnitudes. -/
theorem aux_abs_le_maximum_absolute {x : ℝ} {lo hi : 𝕋} (h1 : toReal lo ≤ x) (h2 : x ≤ toReal hi) :
    |x| ≤ toReal (maximum (absolute lo) (absolute hi)) := by
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  rcases abs_cases x with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; exact le_trans h2 (le_trans (le_abs_self _) (le_max_right _ _))
  · rw [heq]; exact le_trans (neg_le_neg h1) (le_trans (neg_le_abs _) (le_max_left _ _))


-- =======================================  MAIN THEOREM  ======================================= --

/-- An entry of `(E - I_n)G_l` is under the float entry in magnitude. -/
theorem MatExp.abs_genMinus_le {eA : Interval (Mat 𝕋 n n)} {E : Mat ℝ n n}
    (hE : E ∈ eA.construct) (H : Zonotope (Vec 𝕋 n)) (l : Fin H.h) (j : Fin n) :
    |((E - 1) *ᵥ fun i => toReal (H.G l i)) j|
      ≤ toReal (MatExp.genMinus eA H l j) := by -- --- PROOF ---
  -- the member's entries are between the float box's
  have hent := Real.Interval.mem_mat_iff.mp hE
  -- each entry of `E - I_n` is under the float magnitude `genMinus` multiplies by
  have hterm : ∀ k, |(E - 1) j k| ≤ toReal (maximum
      (absolute (if j = k then subDown (eA.inf j k) one else eA.inf j k))
      (absolute (if j = k then subUp (eA.sup j k) one else eA.sup j k))) := by
    intro k
    obtain ⟨h1, h2⟩ := hent j k
    -- on the diagonal the identity moves both ends by one, off it nothing moves
    replace h1 : toReal (eA.inf j k) ≤ E j k := h1
    replace h2 : E j k ≤ toReal (eA.sup j k) := h2
    by_cases hjk : j = k
    · subst hjk
      simp only [if_true]
      refine aux_abs_le_maximum_absolute ?_ ?_
      · have := subDown_le_sub (eA.inf j j) (one : 𝕋)
        rw [toReal_one] at this
        simp only [Matrix.sub_apply, Matrix.one_apply_eq]
        linarith
      · have := sub_le_subUp (eA.sup j j) (one : 𝕋)
        rw [toReal_one] at this
        simp only [Matrix.sub_apply, Matrix.one_apply_eq]
        linarith
    · simp only [hjk, if_false]
      have : (E - 1) j k = E j k := by simp [Matrix.sub_apply, Matrix.one_apply_ne hjk]
      rw [this]
      exact aux_abs_le_maximum_absolute h1 h2
  -- the entry is a sum of products, each under the float product, and the float sum rounds up
  show |∑ k, (E - 1) j k * toReal (H.G l k)| ≤ _
  calc |∑ k, (E - 1) j k * toReal (H.G l k)|
      ≤ ∑ k, |(E - 1) j k * toReal (H.G l k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, toReal (mulUp (maximum
          (absolute (if j = k then subDown (eA.inf j k) one else eA.inf j k))
          (absolute (if j = k then subUp (eA.sup j k) one else eA.sup j k)))
          (absolute (H.G l k))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact le_trans (mul_le_mul (hterm k) (by rw [toReal_absolute]) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hterm k))) (mul_le_mulUp _ _)
    _ ≤ _ := sum_le_sumUp _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
