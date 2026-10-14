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


-- ====================================  `antitone_invSqrt`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- A reciprocal of a monotone square root of a monotone clamp. -/
theorem antitone_invSqrt : Antitone invSqrt := by
  intro a b hab
  unfold invSqrt
  gcongr

end CORALean.Real


-- =================================  `enclosure_exact_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- ℝ-only, as `Enclosure.exact` is: only ℝ stores `σ`'s values. Both ends are `σ`, and reading ℝ
is the identity, so the bracket is two equalities. -/
theorem enclosure_exact_sound (σ : ℝ → ℝ) : (Enclosure.exact σ).Sound σ :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end CORALean.Real


-- =====================================  `evalPoly_coeff`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- ℝ-only, as `evalPoly` is: coefficients indexed by degree, up to the natural degree. -/
theorem evalPoly_coeff (p : Polynomial ℝ) (t : ℝ) :
    evalPoly (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)) t = Polynomial.eval t p := by
  rw [Polynomial.eval_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (p.natDegree + 1)

end CORALean.Real


-- ======================================  `exp_sum_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- A coordinate is what makes the denominator positive, so every statement about softmax takes one
rather than a `NeZero`: at `n = 0` there is nothing to say and the layer's obligation is vacuous. -/
theorem exp_sum_pos (x : Vec ℝ n) (i : Fin n) : 0 < ∑ j, Real.exp (x j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (x j)) ⟨i, Finset.mem_univ i⟩

end CORALean.Real


-- ==================================  `invSqrt_eq_of_one_le`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- The agreement with the unclamped function above the clamp point — the whole reason `invSqrt`
exists rather than `(Real.sqrt ·)⁻¹` directly. -/
theorem invSqrt_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : invSqrt x = (Real.sqrt x)⁻¹ := by
  unfold invSqrt
  rw [max_eq_left hx]

end CORALean.Real


-- ======================================  `invSqrt_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- `max x 1` never reaches zero, so neither does its square root. -/
theorem invSqrt_pos (x : ℝ) : 0 < invSqrt x := by
  unfold invSqrt
  have : (0 : ℝ) < max x 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity

end CORALean.Real


-- ======================================  `le_windowMax`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- The supremum bounds each of its arguments; `Finset.le_sup'` at the window's own index. -/
theorem le_windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : f l ≤ windowMax f :=
  Finset.le_sup' f (Finset.mem_univ l)

end CORALean.Real


-- ===============================  `scaleRounding_exact_sound`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- ℝ-only, as `ScaleRounding.exact` is: only ℝ stores `r · x` exactly. Both directions are the
product itself. -/
theorem scaleRounding_exact_sound (r : ℝ) : (ScaleRounding.exact r).Sound r :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end CORALean.Real


-- ======================================  `sigmoid_pos`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- A reciprocal of `1 + e⁻ᵗ`, which is positive. -/
theorem sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  rw [sigmoid]
  positivity

end CORALean.Real


-- ===================================  `le_sigmoidDerivHi`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- ℝ-only, as `sigmoidDerivLo_le` is: each factor largest at its other end. -/
theorem le_sigmoidDerivHi {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    sigmoidDeriv t ≤ sigmoidDerivHi l u :=
  mul_le_mul (sigmoid_mono hu) (sigmoid_mono (neg_le_neg hl))
    (le_of_lt (sigmoid_pos _)) (le_of_lt (sigmoid_pos _))

end CORALean.Real


-- =====================================  `sigmoid_lt_one`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- `sigmoid_pos` read at the mirrored argument. -/
theorem sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have h := sigmoid_pos (-t)
  rw [sigmoid_neg] at h
  linarith

end CORALean.Real


-- =====================================  `softmax_nonneg`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- A positive numerator over a positive denominator. -/
theorem softmax_nonneg (x : Vec ℝ n) (i : Fin n) : 0 ≤ softmax x i :=
  div_nonneg (Real.exp_pos (x i)).le (exp_sum_pos x i).le

end CORALean.Real


-- ===================================  `softmax_sum_eq_one`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- The constraint the enclosure is built to keep, and a fact a specification may use directly. -/
theorem softmax_sum_eq_one (x : Vec ℝ n) (i : Fin n) : ∑ j, softmax x j = 1 := by
  show ∑ j, Real.exp (x j) / (∑ k, Real.exp (x k)) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (exp_sum_pos x i))

end CORALean.Real


-- ======================================  `windowMax_le`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- The other half of the supremum's characterisation, `Finset.sup'_le`: a bound on every
coordinate bounds the maximum. -/
theorem windowMax_le {k : ℕ} {f : Fin (k + 1) → ℝ} {c : ℝ} (h : ∀ l, f l ≤ c) :
    windowMax f ≤ c :=
  Finset.sup'_le _ f fun l _ => h l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
