module

public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.NN.Layers.Layer
public import Mathlib.Analysis.Complex.Exponential
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# Softmax, and its exact box

CORA's `nnSoftmaxLayer`: `x i ↦ exp(x i) / ∑ⱼ exp(x j)`, the first layer whose output depends on
*every* input coordinate; `Relaxation` cannot express that, so the layer is written directly, with
no slope. The outputs sum to one, and no representation this layer can name keeps that hyperplane;
its shadow on each coordinate is exact for a box: from raw bounds `rl ≤ y ≤ ru`, `y i ∈ [1 - ∑_{j≠i}
ru j, 1 - ∑_{j≠i} rl j]`, intersected with `[rl i, ru i]`. Over ℝ, with both raw bounds, this is the
exact layer; a machine scalar has no total upper bound on an exponential, so the exact box is a
specification the runnable layer does not reproduce.

## Inputs
* `x` – input vector

## Output
* vector of normalised exponentials
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S] [OfInterval S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def softmax (x : Vec ℝ n) : Vec ℝ n :=
  fun i => Real.exp (x i) / ∑ j, Real.exp (x j)

noncomputable def softmaxRawLower (I : Interval (Vec ℝ n)) (i : Fin n) : ℝ :=
  (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (I.sup j - I.inf i))⁻¹

noncomputable def softmaxRawUpper (I : Interval (Vec ℝ n)) (i : Fin n) : ℝ :=
  (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (I.inf j - I.sup i))⁻¹

/-- The raw bounds cut down by what the other coordinates leave over. -/
noncomputable def softmaxBox (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i =>
    max (softmaxRawLower I i) (1 - ∑ j ∈ Finset.univ.erase i, softmaxRawUpper I j)
  sup := fun i =>
    min (softmaxRawUpper I i) (1 - ∑ j ∈ Finset.univ.erase i, softmaxRawLower I j)

/-- A box and nothing else: the slope is zero, so no `mtimes` and no `plus` appear. -/
noncomputable def Layer.softmax : Layer S n n where
  enclose s := ofInterval (softmaxBox (interval s))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
