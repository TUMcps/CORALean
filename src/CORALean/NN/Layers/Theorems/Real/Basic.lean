module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.EvalPoly
public import CORALean.NN.Layers.Definitions.InvSqrt
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Definitions.SigmoidRelaxation
public import CORALean.NN.Layers.Definitions.Softmax
public import CORALean.NN.Layers.Definitions.WindowMax
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono
public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `NN/Layers/Theorems/Real`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- ====================================  `antitone_invSqrt`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- A reciprocal of a monotone square root of a monotone clamp. -/
theorem antitone_invSqrt : Antitone invSqrt := by
  intro a b hab
  unfold invSqrt
  gcongr


-- =================================  `enclosure_exact_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)

/-- ℝ-only, as `Enclosure.exact` is: only ℝ stores `σ`'s values. Both ends are `σ`, and reading ℝ
is the identity, so the bracket is two equalities. -/
theorem enclosure_exact_sound (σ : ℝ → ℝ) : (Enclosure.exact σ).IsSound σ :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩


-- ======================================  `exp_sum_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- A coordinate is what makes the denominator positive, so every statement about softmax takes one
rather than a `NeZero`: at `n = 0` there is nothing to say and the layer's obligation is vacuous. -/
theorem exp_sum_pos (x : Vec ℝ n) (i : Fin n) : 0 < ∑ j, Real.exp (x j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (x j)) ⟨i, Finset.mem_univ i⟩


-- ==================================  `invSqrt_eq_of_one_le`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The agreement with the unclamped function above the clamp point — the whole reason `invSqrt`
exists rather than `(Real.sqrt ·)⁻¹` directly. -/
theorem invSqrt_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : invSqrt x = (Real.sqrt x)⁻¹ := by
  unfold invSqrt
  rw [max_eq_left hx]


-- ======================================  `invSqrt_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `max x 1` never reaches zero, so neither does its square root. -/
theorem invSqrt_pos (x : ℝ) : 0 < invSqrt x := by
  unfold invSqrt
  have : (0 : ℝ) < max x 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity


-- ======================================  `le_windowMax`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The supremum bounds each of its arguments; `Finset.le_sup'` at the window's own index. -/
theorem le_windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : f l ≤ windowMax f :=
  Finset.le_sup' f (Finset.mem_univ l)


-- ======================================  `sigmoid_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- A reciprocal of `1 + e⁻ᵗ`, which is positive. -/
theorem sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  rw [sigmoid]
  positivity


-- ===================================  `le_sigmoidDerivHi`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- ℝ-only, as `sigmoidDerivLo_le` is: each factor largest at its other end. -/
theorem le_sigmoidDerivHi {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDeriv t ≤ sigmoidDerivHi l u :=
  mul_le_mul (sigmoid_mono hu) (sigmoid_mono (neg_le_neg hl))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))


-- =====================================  `softmax_nonneg`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- A positive numerator over a positive denominator. -/
theorem softmax_nonneg (x : Vec ℝ n) (i : Fin n) : 0 ≤ softmax x i :=
  div_nonneg (Real.exp_pos (x i)).le (exp_sum_pos x i).le


-- ======================================  `windowMax_le`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The other half of the supremum's characterisation, `Finset.sup'_le`: a bound on every
coordinate bounds the maximum. -/
theorem windowMax_le {k : ℕ} {f : Fin (k + 1) → ℝ} {c : ℝ} (h : ∀ l, f l ≤ c) :
    windowMax f ≤ c :=
  Finset.sup'_le _ f fun l _ => h l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
