module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.NN.Definitions.ActivationKind
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# `NN/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ===================================  `ActivationKind.fn`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The scalar function: `max t 0`, the logistic function, or `tanh`. -/
noncomputable def ActivationKind.fn : ActivationKind → ℝ → ℝ
  | .relu => Real.relu
  | .sigmoid => Real.sigmoid
  | .tanh => Real.tanh


-- ====================================  `InputOrderMethod`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `method` of `getInputNeuronOrder`: `'in-order'`, `'sensitivity'`, `'snake'`. -/
inductive InputOrderMethod where
  | inOrder
  | sensitivity
  | snake

end CORALean


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  `ScalarEncloses`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- `ScalarEncloses E f`: for every box `I` and every real `x` in it, `f x` lies in the box `E I`.
It is what an activation's stored enclosure owes the real activation or derivative it stands for. -/
def ScalarEncloses (E : Interval 𝕋 → Interval 𝕋) (f : ℝ → ℝ) : Prop :=
  ∀ (I : Interval 𝕋) (x : ℝ), toReal I.inf ≤ x → x ≤ toReal I.sup →
    toReal (E I).inf ≤ f x ∧ f x ≤ toReal (E I).sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
