module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.ClampUnit
public import CORALean.NN.Layers.Operations.DoubleRounding
public import CORALean.NN.Layers.Operations.GeneratorReduction
public import CORALean.NN.Layers.Operations.LeakyRelu
public import CORALean.NN.Layers.Operations.PolyRelaxationFamilyDegOf
public import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
public import CORALean.NN.Layers.Operations.PolyRelaxationToRelaxation
public import CORALean.NN.Layers.Operations.RelaxationToPoly
public import CORALean.NN.Layers.Operations.Sigmoid
public import CORALean.NN.Layers.Operations.SigmoidPoly
public import CORALean.NN.Layers.Operations.SigmoidRelaxation
public import CORALean.NN.Layers.Operations.Square
public import CORALean.NN.Layers.Operations.Tanh
public import CORALean.NN.Layers.Operations.TanhRelaxation
public import CORALean.NN.Layers.Theorems.ActivationPolySound
public import CORALean.NN.Layers.Theorems.ActivationSound
public import CORALean.NN.Layers.Theorems.InvSqrtRootRelaxationSound
public import CORALean.NN.Layers.Theorems.LeakyReluRelaxationSound
public import CORALean.NN.Layers.Theorems.OfAffineConjSound
public import CORALean.NN.Layers.Theorems.OfMonotoneSound
public import CORALean.NN.Layers.Theorems.PadToSound
public import CORALean.NN.Layers.Theorems.Real.EvalPolyOne
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
public import CORALean.NN.Layers.Theorems.SigmoidCurvatureRelaxationSound
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureSound
public import CORALean.NN.Layers.Theorems.SigmoidPolyRelaxationSound
public import CORALean.NN.Layers.Theorems.SquareRelaxationSound
public import CORALean.NN.Layers.Theorems.TighterSound

@[expose] public section

/-!
# `NN/Layers/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `clampUnit_le_one`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `minimum` and `maximum` are exact, so the clamp reads as a value between `0` and `1`. -/
theorem clampUnit_le_one (c : 𝕋) : toReal (clampUnit c) ≤ 1 := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_zero, toReal_one]
  exact max_le zero_le_one (min_le_left _ _)

end CORALean


-- ====================================  `clampUnit_nonneg`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `maximum` is exact, so the clamp is at least the stored `zero`, which reads as `0`. -/
theorem clampUnit_nonneg (c : 𝕋) : 0 ≤ toReal (clampUnit c) := by
  rw [clampUnit, toReal_maximum, toReal_zero]
  exact le_max_left _ _

end CORALean


-- ==================================  `doubleRounding_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Each direction of the self-sum is on its side of `x + x = 2x`. -/
theorem doubleRounding_sound : (doubleRounding (𝕋 := 𝕋)).Sound 2 where
  up_ge x := by have h := add_le_addUp x x; show _ ≤ toReal (addUp x x); linarith
  down_le x := by have h := addDown_le_add x x; show toReal (addDown x x) ≤ _; linarith

end CORALean


-- =============================  `Layer.generatorReduction_sound`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- The identity: `reduce_outer` says the reduced set contains the set, whichever generators are
dropped. -/
theorem Layer.generatorReduction_sound [∀ n, Reduce (S n) (Vec ℝ n)] (n maxGens : ℕ) :
    (Layer.generatorReduction (S := S) n maxGens).Sound id :=
  ⟨fun s _x hx => Reduce.reduce_outer s maxGens hx⟩

end CORALean


-- ================================  `Layer.invSqrtRoot_sound`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `Real.invSqrt` coordinatewise, for every point of every set. -/
theorem Layer.invSqrtRoot_sound (p : ℕ) :
    (Layer.invSqrtRoot (𝕋 := 𝕋) (S := S) (n := n) p).Sound fun x i => Real.invSqrt (x i) :=
  Layer.activation_sound (invSqrtRootRelaxation_sound p)

end CORALean


-- =================================  `Layer.leakyRelu_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `Real.leakyRelu` at the stored `α`, coordinatewise, at every slope, for `α ≤ 1`. -/
theorem Layer.leakyRelu_sound (α : 𝕋) (hα : toReal α ≤ 1) (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.leakyRelu (S := S) (n := n) α lam).Sound fun x i => Real.leakyRelu (toReal α) (x i) :=
  Layer.activation_sound (leakyReluRelaxation_sound α hα lam)

end CORALean


-- ================================  `Layer.sigmoidPoly_sound`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {N : ℕ}

/-- `Real.sigmoid` coordinatewise, which the layer itself never mentions. -/
theorem Layer.sigmoidPoly_sound (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (Layer.sigmoidPoly k c dx p).Sound fun x i => Real.sigmoid (x i) :=
  Layer.activationPoly_sound fun i => sigmoidPolyRelaxation_sound k (c i) (dx i) (p i)

end CORALean


-- ===================================  `Layer.square_sound`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `x ↦ x²` coordinatewise. -/
theorem Layer.square_sound :
    (Layer.square (𝕋 := 𝕋) (S := S) (n := n)).Sound fun x i => x i ^ 2 :=
  Layer.activation_sound (σ := fun x : ℝ => x ^ 2) squareRelaxation_sound

end CORALean


-- ===============================  `PolyRelaxation.padTo_error`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}

/-- By `rfl`, which is what makes it free. -/
theorem PolyRelaxation.padTo_error (P : PolyRelaxation 𝕋 k) (M : ℕ) :
    (P.padTo M).error = P.error := rfl

end CORALean


-- ===========================  `PolyRelaxationFamily.deg_le_degOf`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- What padding needs, and what makes the common degree no restriction. -/
theorem PolyRelaxationFamily.deg_le_degOf (F : PolyRelaxationFamily 𝕋)
    (t : OrderPattern n) (i : Fin n) : F.deg (t i) ≤ F.degOf t :=
  Finset.le_sup (f := fun j => F.deg (t j)) (Finset.mem_univ i)

end CORALean


-- ==========================  `PolyRelaxationFamily.atPattern_sound`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {σ : ℝ → ℝ}

/-- Padding is where each neuron's own degree bound is spent, and it is the only thing the common
degree costs. -/
theorem PolyRelaxationFamily.atPattern_sound {F : PolyRelaxationFamily 𝕋} (hF : F.Sound σ)
    (t : OrderPattern n) (i : Fin n) : (F.atPattern t i).Sound σ :=
  PolyRelaxation.padTo_sound (F.deg_le_degOf t i) (hF.rel_sound (t i))

end CORALean


-- ================================  `Relaxation.toPoly_sound`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}

/-- `sound` read through `evalPoly_one`: the same inequality. -/
theorem Relaxation.toPoly_sound {R : Relaxation 𝕋} (hR : R.Sound σ) : R.toPoly.Sound σ := by
  refine ⟨fun {l u t} hl hu => ?_⟩
  rw [Real.evalPoly_one]
  exact hR.sound hl hu

end CORALean


-- =============================  `Relaxation.toPoly_toRelaxation`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The two round-trip by `rfl`, which is what makes "order 1" a reading of `Relaxation` rather
than a second notion standing beside it. -/
theorem Relaxation.toPoly_toRelaxation (R : Relaxation 𝕋) :
    R.toPoly.toRelaxation = R := rfl

end CORALean


-- ==================================  `rootRelaxation_sound`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `sqrtDown` and `sqrtUp` bracket `Real.sqrt` at every stored value, whatever the fuel `p`,
and `Real.sqrt` is monotone. -/
theorem rootRelaxation_sound (p : ℕ) : (rootRelaxation (𝕋 := 𝕋) p).Sound Real.sqrt :=
  Relaxation.ofMonotone_sound (fun _ _ h => Real.sqrt_le_sqrt h)
    ⟨fun a => sqrtDown_le p a, fun a => le_sqrtUp p a⟩

end CORALean


-- ====================================  `Layer.root_sound`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `Real.sqrt` coordinatewise, for every point of every set. -/
theorem Layer.root_sound (p : ℕ) :
    (Layer.root (𝕋 := 𝕋) (S := S) (n := n) p).Sound fun x i => Real.sqrt (x i) :=
  Layer.activation_sound (rootRelaxation_sound p)

end CORALean


-- ================================  `sigmoidRelaxation_sound`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Both halves are sound at the sound enclosure, so the tighter is too. -/
theorem sigmoidRelaxation_sound (k : ℕ) :
    (sigmoidRelaxation (𝕋 := 𝕋) k).Sound Real.sigmoid :=
  Relaxation.tighter_sound (sigmoidCurvatureRelaxation_sound (sigmoidEnclosure_sound k))
    (Relaxation.ofMonotone_sound Real.sigmoid_mono (sigmoidEnclosure_sound k))

end CORALean


-- ==================================  `Layer.sigmoid_sound`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `Real.sigmoid` coordinatewise, at every reduction depth. -/
theorem Layer.sigmoid_sound (k : ℕ) :
    (Layer.sigmoid (𝕋 := 𝕋) (S := S) (n := n) k).Sound fun x i => Real.sigmoid (x i) :=
  Layer.activation_sound (sigmoidRelaxation_sound k)

end CORALean


-- ==================================  `tanhRelaxation_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The sigmoid relaxation's soundness, transported along the conjugation identity. -/
theorem tanhRelaxation_sound (k : ℕ) : (tanhRelaxation (𝕋 := 𝕋) k).Sound Real.tanh :=
  Relaxation.ofAffineConj_sound (sigmoidRelaxation_sound k) doubleRounding_sound
    doubleRounding_sound (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end CORALean


-- ====================================  `Layer.tanh_sound`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}

/-- `Real.tanh` coordinatewise, at every reduction depth. -/
theorem Layer.tanh_sound (k : ℕ) :
    (Layer.tanh (𝕋 := 𝕋) (S := S) (n := n) k).Sound fun x i => Real.tanh (x i) :=
  Layer.activation_sound (tanhRelaxation_sound k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
