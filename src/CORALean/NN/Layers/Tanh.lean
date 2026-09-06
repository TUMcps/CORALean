import CORALean.NN.Layers.Sigmoid

/-!
# The tanh layer

CORA's `nnTanhLayer`, over Mathlib's `Real.tanh`. Tanh is an affine conjugate of
the logistic function — `tanh t = 2 σ (2 t) - 1` — so nothing about its relaxation
is independent: `Relaxation.ofAffineConj` transports `sigmoidRelaxation` wholesale
rather than rebuilding a derivative bracket for it.

No precision is lost in the move. `tanh' t = (1 + tanh t)(1 - tanh t)
= 4 σ(2t) σ(-2t) = 4 σ'(2t)` (via `sigmoid_neg`), so the transported bracket is
tanh's own, not merely a sound one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

/-- Clearing `e⁻ᵗ` from both sides of `tanh` leaves `(1 - e⁻²ᵗ)/(1 + e⁻²ᵗ)`,
which is `2 σ(2t) - 1`. -/
theorem tanh_eq_sigmoid (t : ℝ) : Real.tanh t = 2 * sigmoid (2 * t) - 1 := by -- --- PROOF ---
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

/-- The identity above differentiated, which is where the header's `4 σ'(2t)`
comes from. Mathlib's own `tanh` derivative is not in scope here. -/
theorem hasDerivAt_tanh (t : ℝ) :
    HasDerivAt Real.tanh (4 * sigmoidDeriv (2 * t)) t := by -- --- PROOF ---
  have hinner : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2:ℝ)
  have hchain : HasDerivAt (fun s : ℝ => sigmoid (2 * s)) (sigmoidDeriv (2 * t) * 2) t :=
    (hasDerivAt_sigmoid (2 * t)).comp t hinner
  have h := (hchain.const_mul (2:ℝ)).sub_const (1:ℝ)
  -- the conjugating affine map, undone on the function and on the value alike
  rw [show (fun s : ℝ => 2 * sigmoid (2 * s) - 1) = Real.tanh from
      funext fun s => (tanh_eq_sigmoid s).symm,
    show 2 * (sigmoidDeriv (2 * t) * 2) = 4 * sigmoidDeriv (2 * t) by ring] at h
  exact h

/-- `sigmoidRelaxation` read through the identity above: `a = b = 2`, `c = -1`. -/
noncomputable def tanhRelaxation : Relaxation Real.tanh :=
  sigmoidRelaxation.ofAffineConj (a := 2) (b := 2) (c := -1) (by norm_num) (by norm_num)
    (fun t => by rw [tanh_eq_sigmoid]; ring)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def tanh : Layer S n n := Layer.activation tanhRelaxation

end Layer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
