import CORALean.NN.Layers.Curvature

/-!
# The sigmoid layer

CORA's `nnSigmoidLayer`, defined here because Mathlib has no logistic function
and stated as `(1 + e⁻ᵗ)⁻¹` so that monotonicity is the denominator's.

`σ' t = σ t · σ (-t)` is what gives the relaxation a slope: one factor rises and
the other falls, so the ends of a neuron's range bracket the derivative over it
with two monotonicity steps and no case on where zero lies. `Relaxation.ofDeriv`
turns that bracket into the secant slope, clamped into it, and an error of half
the bracket's width times the box width.

On a narrow box the bracket is tight and that error is quadratic in the width,
so the slope is nearly free. On a wide one — above all across zero, where the
two curvature regions pull the ends apart — it is loose, and `tighter` falls
back on `Relaxation.ofMonotone` and slope zero.

`Float.Layer.sigmoid` is the same pair over `Float.sigmoidEnclosure`, which
supplies `σ` at the ends and, as a product, `σ'`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

noncomputable def sigmoid (t : ℝ) : ℝ := (1 + Real.exp (-t))⁻¹

theorem sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  rw [sigmoid]
  positivity

theorem sigmoid_mono : Monotone sigmoid := by
  intro a b hab
  have hpb : (0:ℝ) < 1 + Real.exp (-b) := by positivity
  have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  show (1 + Real.exp (-a))⁻¹ ≤ (1 + Real.exp (-b))⁻¹
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpb (by linarith)

/-- Mirroring the argument complements the value, which is what makes the
derivative below a product of two sigmoids. -/
theorem sigmoid_neg (t : ℝ) : sigmoid (-t) = 1 - sigmoid t := by
  have hden : (1:ℝ) + Real.exp t ≠ 0 := by positivity
  have hden' : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
  rw [sigmoid, sigmoid, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- Below one, which is `sigmoid_pos` read at the mirrored argument. -/
theorem sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have h := sigmoid_pos (-t)
  rw [sigmoid_neg] at h
  linarith

/-! ## The derivative, and its bracket over a box

Stated as `σ t · σ (-t)` rather than `σ t (1 - σ t)`: written that way each
factor is monotone in `t` on its own, so a box's ends bracket the product. -/

noncomputable def sigmoidDeriv (t : ℝ) : ℝ := sigmoid t * sigmoid (-t)

/-- A product of two sigmoids, so inside `(0, 1)` on all of ℝ: the global bound
a refinement level's fit is chosen against. -/
theorem abs_sigmoidDeriv_le_one (t : ℝ) : |sigmoidDeriv t| ≤ 1 := by
  have h1 := sigmoid_pos t
  have h2 := sigmoid_pos (-t)
  have h3 := sigmoid_lt_one t
  have h4 := sigmoid_lt_one (-t)
  show |sigmoid t * sigmoid (-t)| ≤ 1
  rw [abs_le]
  exact ⟨by nlinarith, by nlinarith⟩

theorem hasDerivAt_sigmoid (t : ℝ) : HasDerivAt sigmoid (sigmoidDeriv t) t := by
  have hEpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
  have hden : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * -1) t :=
    (hasDerivAt_neg t).exp
  have hinv := (hexp.const_add (1:ℝ)).inv (by exact hden)
  -- the two negations cancel and `exp t` is `exp (-t)⁻¹`, which leaves one field identity
  have hkey : -(Real.exp (-t) * -1) / (1 + Real.exp (-t)) ^ 2 = sigmoidDeriv t := by
    have hE : Real.exp (-t) ≠ 0 := ne_of_gt hEpos
    have hEt : Real.exp t = (Real.exp (-t))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [sigmoidDeriv, sigmoid, sigmoid, neg_neg, hEt]
    field_simp
    ring
  rw [← hkey]
  exact hinv

/-- The bracket a box gives: `σ` rises with its argument and `σ (-·)` falls, so
each factor is largest at one end and smallest at the other. -/
noncomputable def sigmoidDerivLo (l u : ℝ) : ℝ := sigmoid l * sigmoid (-u)

noncomputable def sigmoidDerivHi (l u : ℝ) : ℝ := sigmoid u * sigmoid (-l)

theorem sigmoidDerivLo_le {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDerivLo l u ≤ sigmoidDeriv t :=
  mul_le_mul (sigmoid_mono hl) (sigmoid_mono (neg_le_neg hu))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))

theorem le_sigmoidDerivHi {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDeriv t ≤ sigmoidDerivHi l u :=
  mul_le_mul (sigmoid_mono hu) (sigmoid_mono (neg_le_neg hl))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))

/-! ## The relaxation

The secant is the slope a curvature argument points at, and clamping it into the
bracket is what makes it a precision choice: any value in the bracket is sound,
and the clamp is what a box of width zero, where the secant is `0 / 0`, needs. -/

noncomputable def sigmoidSlope (l u : ℝ) : ℝ :=
  max (sigmoidDerivLo l u) (min (sigmoidDerivHi l u) ((sigmoid u - sigmoid l) / (u - l)))

noncomputable def sigmoidCurvatureRelaxation : Relaxation sigmoid :=
  Relaxation.ofDeriv hasDerivAt_sigmoid sigmoidDerivLo sigmoidDerivHi sigmoidSlope
    (fun _ _ _ h₁ h₂ => sigmoidDerivLo_le h₁ h₂) (fun _ _ _ h₁ h₂ => le_sigmoidDerivHi h₁ h₂)
    fun _ _ h => ⟨le_max_left _ _,
      max_le (le_trans (sigmoidDerivLo_le le_rfl h) (le_sigmoidDerivHi le_rfl h))
        (min_le_left _ _)⟩

/-- The curvature relaxation where its bracket pays for itself, and the monotone
one — slope zero, the output range — where it does not. -/
noncomputable def sigmoidRelaxation : Relaxation sigmoid :=
  sigmoidCurvatureRelaxation.tighter (Relaxation.ofMonotone sigmoid_mono)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def sigmoid : Layer S n n := Layer.activation sigmoidRelaxation

end Layer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
