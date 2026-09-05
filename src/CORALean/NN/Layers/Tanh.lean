import CORALean.NN.Layers.Sigmoid

/-!
# The tanh layer

CORA's `nnTanhLayer`, over Mathlib's `Real.tanh`, which has no monotonicity
lemma; `tanh_mono` supplies one by clearing the two denominators, where what
is left is `e^{b-a} ≥ e^{a-b}`.

Tanh is a rescaled sigmoid — `tanh t = 2 σ(2t) - 1`, which is where its
derivative comes from — and the relaxation is the same shape: `1 - tanh² t`
written as `(1 + tanh t)(1 - tanh t)`, one factor rising and one falling, so a
neuron's range brackets the derivative over it and `Relaxation.ofDeriv` turns
that into a slope. `tighter` keeps it only where it beats slope zero, which is
on boxes narrow enough for the bracket to be tight.

The float counterpart is `Float.Layer.tanh`, and it takes the rescaling
literally: `Float.sigmoidEnclosure` is reused rather than a second exponential
enclosure written, and `tanh_eq_sigmoid` is the identity both layers read it by.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

/-- Both denominators are positive, so the claim is `e^{a-b} ≤ e^{b-a}`. -/
theorem tanh_mono : Monotone Real.tanh := by
  intro a b hab
  rw [Real.tanh_eq, Real.tanh_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp a * Real.exp (-b) = Real.exp (a - b) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  have h₂ : Real.exp b * Real.exp (-a) = Real.exp (b - a) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  have key : Real.exp (a - b) ≤ Real.exp (b - a) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Clearing `e⁻ᵗ` from both sides of `tanh` leaves `(1 - e⁻²ᵗ)/(1 + e⁻²ᵗ)`,
which is `2 σ(2t) - 1`. -/
theorem tanh_eq_sigmoid (t : ℝ) : Real.tanh t = 2 * sigmoid (2 * t) - 1 := by
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hE : Real.exp t ≠ 0 := ne_of_gt hpos
  have h₁ : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have h₂ : Real.exp (-(2 * t)) = (Real.exp t * Real.exp t)⁻¹ := by
    rw [Real.exp_neg, two_mul, Real.exp_add]
  have hA : Real.exp t + (Real.exp t)⁻¹ ≠ 0 := by positivity
  have hB : (1:ℝ) + (Real.exp t * Real.exp t)⁻¹ ≠ 0 := by positivity
  rw [Real.tanh_eq, sigmoid, h₁, h₂]
  field_simp
  ring

/-! ## The derivative, and its bracket over a box

`1 - tanh²` as a product of `1 ± tanh`, so that each factor is monotone in `t`
on its own and a box's ends bracket the product. -/

noncomputable def tanhDeriv (t : ℝ) : ℝ := (1 + Real.tanh t) * (1 - Real.tanh t)

theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (tanhDeriv t) t := by
  have hfun : Real.tanh = fun x => 2 * sigmoid (2 * x) - 1 := funext tanh_eq_sigmoid
  have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2:ℝ)
  have hcomp : HasDerivAt (fun x : ℝ => sigmoid (2 * x)) (sigmoidDeriv (2 * t) * 2) t :=
    (hasDerivAt_sigmoid (2 * t)).comp t hlin
  have hchain := (hcomp.const_mul (2:ℝ)).sub_const (1:ℝ)
  -- `2 σ(±2t)` is `1 ± tanh t`, so the chain rule's `4 σ'(2t)` is the product form
  have hkey : 2 * (sigmoidDeriv (2 * t) * 2) = tanhDeriv t := by
    have hup : 2 * sigmoid (2 * t) = 1 + Real.tanh t := by rw [tanh_eq_sigmoid]; ring
    have hdown : 2 * sigmoid (-(2 * t)) = 1 - Real.tanh t := by
      have hneg := tanh_eq_sigmoid (-t)
      rw [Real.tanh_neg, show (2:ℝ) * -t = -(2 * t) by ring] at hneg
      linarith
    rw [tanhDeriv, sigmoidDeriv, ← hup, ← hdown]
    ring
  rw [hfun, ← hkey]
  exact hchain

/-- The bracket a box gives: `tanh` rises, so `1 + tanh` is largest at the right
end and `1 - tanh` at the left, and both factors are positive throughout. -/
noncomputable def tanhDerivLo (l u : ℝ) : ℝ := (1 + Real.tanh l) * (1 - Real.tanh u)

noncomputable def tanhDerivHi (l u : ℝ) : ℝ := (1 + Real.tanh u) * (1 - Real.tanh l)

theorem tanhDerivLo_le {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    tanhDerivLo l u ≤ tanhDeriv t :=
  mul_le_mul (by linarith [tanh_mono hl]) (by linarith [tanh_mono hu])
    (by linarith [Real.tanh_lt_one u]) (by linarith [Real.neg_one_lt_tanh t])

theorem le_tanhDerivHi {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    tanhDeriv t ≤ tanhDerivHi l u :=
  mul_le_mul (by linarith [tanh_mono hu]) (by linarith [tanh_mono hl])
    (by linarith [Real.tanh_lt_one t]) (by linarith [Real.neg_one_lt_tanh u])

/-! ## The relaxation

As for sigmoid: the secant clamped into the bracket, which is what a box of
width zero needs, and the monotone relaxation wherever the bracket is too loose
to pay for the slope it carries. -/

noncomputable def tanhSlope (l u : ℝ) : ℝ :=
  max (tanhDerivLo l u) (min (tanhDerivHi l u) ((Real.tanh u - Real.tanh l) / (u - l)))

noncomputable def tanhCurvatureRelaxation : Relaxation Real.tanh :=
  Relaxation.ofDeriv hasDerivAt_tanh tanhDerivLo tanhDerivHi tanhSlope
    (fun _ _ _ h₁ h₂ => tanhDerivLo_le h₁ h₂) (fun _ _ _ h₁ h₂ => le_tanhDerivHi h₁ h₂)
    fun _ _ h => ⟨le_max_left _ _,
      max_le (le_trans (tanhDerivLo_le le_rfl h) (le_tanhDerivHi le_rfl h)) (min_le_left _ _)⟩

/-- The curvature relaxation where its bracket pays for itself, and the monotone
one — slope zero, the output range — where it does not. -/
noncomputable def tanhRelaxation : Relaxation Real.tanh :=
  tanhCurvatureRelaxation.tighter (Relaxation.ofMonotone tanh_mono)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

noncomputable def tanh : Layer S n n := Layer.activation tanhRelaxation

end Layer

end CORALean.Real
