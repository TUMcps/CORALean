module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.RelaxationOfDeriv
public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import CORALean.NN.Layers.Operations.RelaxationTighter

@[expose] public section

/-!
# The sigmoid relaxation over ℝ

What the sigmoid layer's relaxation is with `σ` itself at the box's ends: the exact bracket `σ l
σ(-u) ≤ σ' ≤ σ u σ(-l)`, the secant clamped into it as the slope, and `Relaxation.ofDeriv` against
it, kept only where it beats `Relaxation.ofMonotone`. The same constructors a machine scalar runs,
at `𝕋 := ℝ`; what a machine scalar builds from a truncated exponential is looser, so this is a
specification the runnable layer does not reproduce. On a narrow box the bracket is tight and the
error quadratic in the width; on a wide one it is loose, and `tighter` falls back on slope zero.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* lower end of the sigmoid's derivative bracket
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower end of the derivative bracket a box gives. -/
noncomputable def sigmoidDerivLo (l u : ℝ) : ℝ := sigmoid l * sigmoid (-u)

/-- The upper end, each factor at its other end. -/
noncomputable def sigmoidDerivHi (l u : ℝ) : ℝ := sigmoid u * sigmoid (-l)

/-- The secant clamped into the bracket, which a box of width zero, the secant `0 / 0`, needs. -/
noncomputable def sigmoidSlope (l u : ℝ) : ℝ :=
  max (sigmoidDerivLo l u) (min (sigmoidDerivHi l u) ((sigmoid u - sigmoid l) / (u - l)))

/-- The sigmoid relaxation from the exact derivative bracket and the clamped secant slope, with the
exact sigmoid at the box's ends. -/
noncomputable def sigmoidCurvatureRelaxation : Relaxation ℝ :=
  Relaxation.ofDeriv (Enclosure.exact sigmoid) sigmoidDerivLo sigmoidDerivHi sigmoidSlope

/-- The curvature relaxation where its bracket pays for itself, the monotone one elsewhere. -/
noncomputable def sigmoidRelaxation : Relaxation ℝ :=
  Relaxation.tighter sigmoidCurvatureRelaxation (Relaxation.ofMonotone (Enclosure.exact sigmoid))

/-- The sigmoid layer at the exact relaxation. -/
noncomputable def Layer.sigmoid : Layer S n n := CORALean.Layer.activation sigmoidRelaxation

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
