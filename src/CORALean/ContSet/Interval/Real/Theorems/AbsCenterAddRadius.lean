module

public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `|center| + rad` is `absMax`

On a nonempty box the matrix `|center| + rad` that `norm` evaluates is the entrywise
`max |inf| |sup|`: `(a + b) / 2` has the sign of the end of larger magnitude, and adding the
half-width reaches that end.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Entrywise, `|center| + rad = absMax` on a nonempty box. -/
theorem Interval.abs_center_add_radius (A : Interval (Mat ℝ m n))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) (i : Fin m) (j : Fin n) :
    |A.center i j| + A.radius i j = A.absMax i j := by -- --- PROOF ---
  have hc : A.center i j = (A.inf i j + A.sup i j) / 2 := by
    simp only [Interval.center, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
  have hr : A.radius i j = (A.sup i j - A.inf i j) / 2 := by
    simp only [Interval.radius, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
  have h := hA i j
  rw [hc, hr, Interval.absMax]
  rcases le_total 0 (A.inf i j + A.sup i j) with hs | hs
  · rw [abs_of_nonneg (by linarith : 0 ≤ (A.inf i j + A.sup i j) / 2),
      abs_of_nonneg (by linarith : 0 ≤ A.sup i j),
      max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)]
    ring
  · rw [abs_of_nonpos (by linarith : (A.inf i j + A.sup i j) / 2 ≤ 0),
      abs_of_nonpos (by linarith : A.inf i j ≤ 0),
      max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
