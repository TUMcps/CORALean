module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Definitions.Basic
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
public import CORALean.NN.Layers.Theorems.ActivationPolyEncloses
public import CORALean.NN.Layers.Theorems.ActivationEncloses
public import CORALean.NN.Layers.Theorems.InvSqrtRootRelaxationSound
public import CORALean.NN.Layers.Theorems.LeakyReluRelaxationSound
public import CORALean.NN.Layers.Theorems.OfAffineConjSound
public import CORALean.NN.Layers.Theorems.OfMonotoneSound
public import CORALean.NN.Layers.Theorems.PadToSound
public import CORALean.NN.Layers.Theorems.Real.EvalPolyOne
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
public import CORALean.NN.Layers.Theorems.SigmoidRelaxationSound
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


namespace CORALean

section

open Float Float.FloatOps Float.SoundFloatArithmetic

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k n m : ℕ} {σ : ℝ → ℝ} {N : ℕ}


-- ====================================  `clampUnit_le_one`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `minimum` and `maximum` are exact, so the clamp reads as a value between `0` and `1`. -/
theorem clampUnit_le_one (c : 𝕋) : toReal (clampUnit c) ≤ 1 := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_zero, toReal_one]
  exact max_le zero_le_one (min_le_left _ _)


-- ====================================  `clampUnit_nonneg`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `maximum` is exact, so the clamp is at least the stored `zero`, which reads as `0`. -/
theorem clampUnit_nonneg (c : 𝕋) : 0 ≤ toReal (clampUnit c) := by
  rw [clampUnit, toReal_maximum, toReal_zero]
  exact le_max_left _ _


-- ==================================  `doubleRounding_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- Each direction of the self-sum is on its side of `x + x = 2x`. -/
theorem doubleRounding_sound : (doubleRounding (𝕋 := 𝕋)).Sound 2 where
  up_ge x := by have h := add_le_addUp x x; show _ ≤ toReal (addUp x x); linarith
  down_le x := by have h := addDown_le_add x x; show toReal (addDown x x) ≤ _; linarith


-- ===============================  `Layer.sigmoidPoly_encloses`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `Real.sigmoid` coordinatewise, which the layer itself never mentions. -/
theorem Layer.sigmoidPoly_encloses (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (Layer.sigmoidPoly k c dx p).Encloses fun x i => Real.sigmoid (x i) :=
  Layer.activationPoly_encloses fun i => sigmoidPolyRelaxation_sound k (c i) (dx i) (p i)


-- ===============================  `PolyRelaxation.padTo_error`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- By `rfl`, which is what makes it free. -/
theorem PolyRelaxation.padTo_error (P : PolyRelaxation 𝕋 k) (M : ℕ) :
    (P.padTo M).error = P.error := rfl


-- ===========================  `PolyRelaxationFamily.deg_le_degOf`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- What padding needs, and what makes the common degree no restriction. -/
theorem PolyRelaxationFamily.deg_le_degOf (F : PolyRelaxationFamily 𝕋)
    (t : OrderPattern n) (i : Fin n) : F.deg (t i) ≤ F.degOf t :=
  Finset.le_sup (f := fun j => F.deg (t j)) (Finset.mem_univ i)


-- ==========================  `PolyRelaxationFamily.atPattern_sound`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- Padding is where each neuron's own degree bound is spent, and it is the only thing the common
degree costs. -/
theorem PolyRelaxationFamily.atPattern_sound {F : PolyRelaxationFamily 𝕋} (hF : F.Sound σ)
    (t : OrderPattern n) (i : Fin n) : (F.atPattern t i).Sound σ :=
  PolyRelaxation.padTo_sound (F.deg_le_degOf t i) (hF.rel_sound (t i))


-- ================================  `Relaxation.toPoly_sound`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `sound` read through `evalPoly_one`: the same inequality. -/
theorem Relaxation.toPoly_sound {R : Relaxation 𝕋} (hR : R.Sound σ) : R.toPoly.Sound σ := by
  refine ⟨fun {l u t} hl hu => ?_⟩
  rw [Real.evalPoly_one]
  exact hR.sound hl hu


-- =============================  `Relaxation.toPoly_toRelaxation`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The two round-trip by `rfl`, which is what makes "order 1" a reading of `Relaxation` rather
than a second notion standing beside it. -/
theorem Relaxation.toPoly_toRelaxation (R : Relaxation 𝕋) :
    R.toPoly.toRelaxation = R := rfl


-- ==================================  `rootRelaxation_sound`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sqrtDown` and `sqrtUp` bracket `Real.sqrt` at every stored value, whatever the fuel `p`,
and `Real.sqrt` is monotone. -/
theorem rootRelaxation_sound (p : ℕ) : (rootRelaxation (𝕋 := 𝕋) p).Sound Real.sqrt :=
  Relaxation.ofMonotone_sound (fun _ _ h => Real.sqrt_le_sqrt h)
    ⟨fun a => sqrtDown_le p a, fun a => le_sqrtUp p a⟩


-- ==================================  `tanhRelaxation_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- The sigmoid relaxation's soundness, transported along the conjugation identity. -/
theorem tanhRelaxation_sound (k : ℕ) : (tanhRelaxation (𝕋 := 𝕋) k).Sound Real.tanh :=
  Relaxation.ofAffineConj_sound (sigmoidRelaxation_sound k) doubleRounding_sound
    doubleRounding_sound (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end


section

universe u

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}
  {f : Vec ℝ n → Vec ℝ m} {g : Vec ℝ m → Vec ℝ k}


-- ================================  `Enclose.toLayer_encloses`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- What forgetting the kind keeps: the layer is sound at its kind's `eval`. -/
theorem Enclose.toLayer_encloses {L : ℕ → ℕ → Type u} [Enclose L S] (l : L n m) :
    (Enclose.toLayer (S := S) l).Encloses (Enclose.eval (S := S) l).out :=
  ⟨fun s _x hx => Enclose.enclose_outer l s (Set.mem_image_of_mem _ hx)⟩


-- ==================================  `Layer.comp_encloses`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Composition of layers is sound at the composition of their functions. -/
theorem Layer.comp_encloses {L₂ : Layer S m k} {L₁ : Layer S n m} (h₂ : L₂.Encloses g)
    (h₁ : L₁.Encloses f) : (L₂.comp L₁).Encloses (g ∘ f) :=
  ⟨fun s x hx => h₂.enclose_outer _ _ (h₁.enclose_outer s x hx)⟩


-- ==================================  `Layer.Encloses.congr`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Soundness is stable under replacing the function by one that agrees with it
everywhere, which is what lets a caller name the map in its own terms. -/
theorem Layer.Encloses.congr {L : Layer S n m} {f' : Vec ℝ n → Vec ℝ m} (h : L.Encloses f)
    (hff : ∀ x, f' x = f x) : L.Encloses f' :=
  ⟨fun s x hx => (hff x) ▸ h.enclose_outer s x hx⟩


-- ==============================  `Layer.Encloses.image_subset`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- The obligation as an inclusion, which is the form it composes in. -/
theorem Layer.Encloses.image_subset {L : Layer S n m} (h : L.Encloses f) (s : S n) :
    f '' construct s ⊆ construct (L.enclose s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact h.enclose_outer s x hx


-- ================================  `Layer.identity_encloses`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- The identity layer is sound at the identity function. -/
theorem Layer.identity_encloses : (Layer.identity S n).Encloses id := ⟨fun _ _ hx => hx⟩

end


section

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ===========================  `Layer.generatorReduction_encloses`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The identity: `reduce_outer` says the reduced set contains the set, whichever generators are
dropped. -/
theorem Layer.generatorReduction_encloses [∀ n, Reduce (S n) (Vec ℝ n)] (n maxGens : ℕ) :
    (Layer.generatorReduction (S := S) n maxGens).Encloses id :=
  ⟨fun s _x hx => Reduce.reduce_outer s maxGens hx⟩

end


section

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- ===============================  `Layer.invSqrtRoot_encloses`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Real.invSqrt` coordinatewise, for every point of every set. -/
theorem Layer.invSqrtRoot_encloses (p : ℕ) :
    (Layer.invSqrtRoot (𝕋 := 𝕋) (S := S) (n := n) p).Encloses fun x i => Real.invSqrt (x i) :=
  Layer.activation_encloses (invSqrtRootRelaxation_sound p)


-- ================================  `Layer.leakyRelu_encloses`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Real.leakyRelu` at the stored `α`, coordinatewise, at every slope, for `α ≤ 1`. -/
theorem Layer.leakyRelu_encloses (α : 𝕋) (hα : toReal α ≤ 1) (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.leakyRelu (S := S) (n := n) α lam).Encloses fun x i => Real.leakyRelu (toReal α) (x i) :=
  Layer.activation_encloses (leakyReluRelaxation_sound α hα lam)


-- ==================================  `Layer.root_encloses`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Real.sqrt` coordinatewise, for every point of every set. -/
theorem Layer.root_encloses (p : ℕ) :
    (Layer.root (𝕋 := 𝕋) (S := S) (n := n) p).Encloses fun x i => Real.sqrt (x i) :=
  Layer.activation_encloses (rootRelaxation_sound p)


-- =================================  `Layer.sigmoid_encloses`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `Real.sigmoid` coordinatewise, at every reduction depth. -/
theorem Layer.sigmoid_encloses (k : ℕ) :
    (Layer.sigmoid (𝕋 := 𝕋) (S := S) (n := n) k).Encloses fun x i => Real.sigmoid (x i) :=
  Layer.activation_encloses (sigmoidRelaxation_sound k)


-- =================================  `Layer.square_encloses`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `x ↦ x²` coordinatewise. -/
theorem Layer.square_encloses :
    (Layer.square (𝕋 := 𝕋) (S := S) (n := n)).Encloses fun x i => x i ^ 2 :=
  Layer.activation_encloses (σ := fun x : ℝ => x ^ 2) squareRelaxation_sound


-- ==================================  `Layer.tanh_encloses`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

/-- `Real.tanh` coordinatewise, at every reduction depth. -/
theorem Layer.tanh_encloses (k : ℕ) :
    (Layer.tanh (𝕋 := 𝕋) (S := S) (n := n) k).Encloses fun x i => Real.tanh (x i) :=
  Layer.activation_encloses (tanhRelaxation_sound k)

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
