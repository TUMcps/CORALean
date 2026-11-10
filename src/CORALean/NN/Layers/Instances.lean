module

public import CORALean.ContSet.Interval.Float.Theorems.NonemptyHullIsNonempty
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.NN.Layers.Definitions.ActivationLayer
public import CORALean.NN.Layers.Definitions.ActivationPolyLayer
public import CORALean.NN.Layers.Definitions.AvgPoolLayer
public import CORALean.NN.Layers.Definitions.BatchNormLayer
public import CORALean.NN.Layers.Definitions.ConvLayer
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Definitions.LinearWithErrorLayer
public import CORALean.NN.Layers.Definitions.MaxPoolLayer
public import CORALean.NN.Layers.Definitions.ReluLayer
public import CORALean.NN.Layers.Definitions.SigmoidLayer
public import CORALean.NN.Layers.Definitions.SigmoidPolyLayer
public import CORALean.NN.Layers.Definitions.SoundLayer
public import CORALean.NN.Layers.Definitions.SoftmaxLayer
public import CORALean.NN.Layers.Definitions.TanhLayer
public import CORALean.NN.Layers.Theorems.ActivationPolyEncloses
public import CORALean.NN.Layers.Theorems.ActivationEncloses
public import CORALean.NN.Layers.Theorems.AvgPoolEncloses
public import CORALean.NN.Layers.Theorems.BatchNormEncloses
public import CORALean.NN.Layers.Theorems.ConvEncloses
public import CORALean.NN.Layers.Theorems.LinearEncloses
public import CORALean.NN.Layers.Theorems.LinearWithErrorEncloses
public import CORALean.NN.Layers.Theorems.MaxPoolEncloses
public import CORALean.NN.Layers.Theorems.ReluEncloses
public import CORALean.NN.Layers.Theorems.ReshapeEncloses
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.SoftmaxEncloses

@[expose] public section

/-!
# Every standard layer kind, as an `Enclose` instance

Each instance is the kind's layer in `Operations/`, the function its theorem in `Theorems/`
names as `eval`, and that theorem as `enclose_outer`: nothing is proved here that was not
proved of the layer already. Written once over the scalar, so each is the kind at `ℝ` and at
every machine scalar alike, and each asks of the set only the operations its layer calls.

A kind that keeps the dimension matches on its `dim` to learn the two dimensions agree,
which is a cast the compiler erases.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet ContSetLike Float Float.SoundFloatArithmetic
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

/-- `Layer.linear`, at the affine map the weights denote. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.OfInterval ContSet 𝕋] :
    Enclose (LinearLayer 𝕋) ContSet where
  eval L := Erased.mk fun x => toRealMat L.W *ᵥ x + toRealVec L.b
  enclose L := (Layer.linear (S := ContSet) L.W L.b).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.linear_encloses L.W L.b).image_subset S

/-- `Layer.linearWithError` at the box's nonempty hull, committing to its center. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.OfInterval ContSet 𝕋] :
    Enclose (LinearWithErrorLayer 𝕋) ContSet where
  eval L := Erased.mk fun x =>
    toRealMat L.W *ᵥ x + toRealVec L.b + L.E.nonemptyHull.nominal.center
  enclose L := (Layer.linearWithError (S := ContSet) L.W L.b L.E.nonemptyHull).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.linearWithError_encloses L.W L.b _ L.E.nonemptyHull_isNonempty).image_subset S

/-- `Layer.relu`, at `relu` coordinatewise. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.IntervalOuter ContSet 𝕋]
    [Float.OfInterval ContSet 𝕋] : Enclose (ReluLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.relu (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨lam, rfl⟩ => (Layer.relu (S := ContSet) lam).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨lam, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.relu_encloses lam).image_subset S

/-- `Layer.sigmoid`, at the sigmoid coordinatewise. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.IntervalOuter ContSet 𝕋]
    [Float.OfInterval ContSet 𝕋] : Enclose (SigmoidLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.sigmoid (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨k, rfl⟩ => (Layer.sigmoid (𝕋 := 𝕋) (S := ContSet) k).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.sigmoid_encloses k).image_subset S

/-- `Layer.tanh`, at `tanh` coordinatewise. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.IntervalOuter ContSet 𝕋]
    [Float.OfInterval ContSet 𝕋] : Enclose (TanhLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.tanh (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨k, rfl⟩ => (Layer.tanh (𝕋 := 𝕋) (S := ContSet) k).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.tanh_encloses k).image_subset S

/-- `Layer.softmax`, asking of the set only the two boxes. -/
instance [Float.IntervalOuter ContSet 𝕋] [Float.OfInterval ContSet 𝕋] :
    Enclose (SoftmaxLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, rfl⟩ => Erased.mk Real.softmax
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨k, rfl⟩ => (Layer.softmax (𝕋 := 𝕋) (S := ContSet) k).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.softmax_encloses (𝕋 := 𝕋) k).image_subset S

/-- `Layer.activation`, at the `σ` the weights' proof names. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.IntervalOuter ContSet 𝕋]
    [Float.OfInterval ContSet 𝕋] : Enclose (ActivationLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, hR, rfl⟩ => Erased.mk fun x i => hR.choose (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨R, _, rfl⟩ => (Layer.activation (S := ContSet) R).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨_, hR, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.activation_encloses hR.choose_spec).image_subset S

/-- `Layer.batchNorm`, each coordinate scaled and shifted by its channel. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.OfInterval ContSet 𝕋] :
    Enclose (BatchNormLayer 𝕋) ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ =>
      Erased.mk fun x i => toReal (scale (chan i)) * x i + toReal (shift (chan i))
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ =>
      (Layer.batchNorm (S := ContSet) chan scale shift).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.batchNorm_encloses chan scale shift).image_subset S

/-- `Layer.conv`, the stencil read as a sum. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.OfInterval ContSet 𝕋] :
    Enclose (ConvLayer 𝕋) ContSet where
  eval L := Erased.mk fun x j => (∑ i, toReal (L.K (L.chan j) i) * x (L.tap j i)) + toReal (L.b j)
  enclose L := (Layer.conv (S := ContSet) L.chan L.tap L.K L.b).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.conv_encloses L.chan L.tap L.K L.b L.tap_injective).image_subset S

/-- `Layer.avgPool`, the window sum scaled by the stored reciprocal. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.OfInterval ContSet 𝕋] :
    Enclose (AvgPoolLayer 𝕋) ContSet where
  eval L := Erased.mk fun x j => toReal L.winv * ∑ i, x (L.tap j i)
  enclose L := (Layer.avgPool (S := ContSet) L.winv L.tap).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.avgPool_encloses L.winv L.tap L.tap_injective).image_subset S

/-- `Layer.maxPool`, at each window's maximum. -/
instance [∀ n, Plus (ContSet n) (Vec ℝ n)] [Mtimes (Mat 𝕋) ContSet] [Float.IntervalOuter ContSet 𝕋]
    [Float.OfInterval ContSet 𝕋] : Enclose (MaxPoolLayer 𝕋) ContSet where
  eval L := Erased.mk fun x j => Real.windowMax fun i => x (L.tap j i)
  enclose L := (Layer.maxPool (S := ContSet) L.tap L.pivot).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.maxPool_encloses L.tap L.pivot).image_subset S

/-- `Layer.reshape`, asking of the set only `Reindex`. -/
instance [Reindex ContSet] : Enclose ReshapeLayer ContSet where
  eval L := Erased.mk (reindexLin L.e)
  enclose L := (Layer.reshape (S := ContSet) L.e).enclose
  enclose_outer L S := by
    rw [Erased.out_mk]
    exact (Layer.reshape_encloses L.e).image_subset S

/-- `Layer.identity`, asking of the set nothing at all. -/
instance : Enclose IdentityLayer ContSet where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨rfl⟩ => Erased.mk id
  enclose := fun {n m} L => match n, m, L with
    | k, _, ⟨rfl⟩ => (Layer.identity ContSet k).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨rfl⟩ => by
      rw [Erased.out_mk]
      exact Layer.identity_encloses.image_subset S

/-- `Layer.sigmoidPoly`, at a polynomial zonotope. -/
instance : Enclose (SigmoidPolyLayer 𝕋) 𝒫𝒵[𝕋] where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, _, _, _, _, _, rfl⟩ => Erased.mk fun x i => Real.sigmoid (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨k, _, _, c, dx, p, rfl⟩ => (Layer.sigmoidPoly k c dx p).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨k, _, _, c, dx, p, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.sigmoidPoly_encloses k c dx p).image_subset S

/-- `Layer.activationPoly`, at a polynomial zonotope. -/
instance : Enclose (ActivationPolyLayer 𝕋) 𝒫𝒵[𝕋] where
  eval := fun {n m} L => match n, m, L with
    | _, _, ⟨_, _, hP, rfl⟩ => Erased.mk fun x i => hP.choose (x i)
  enclose := fun {n m} L => match n, m, L with
    | _, _, ⟨_, P, _, rfl⟩ => (Layer.activationPoly P).enclose
  enclose_outer := fun {n m} L S => match n, m, L with
    | _, _, ⟨_, _, hP, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.activationPoly_encloses hP.choose_spec).image_subset S

/-- A packed layer, its three fields read back. -/
instance : Enclose (SoundLayer ContSet) ContSet where
  eval L := L.eval
  enclose L := L.enclose
  enclose_outer L := L.enclose_outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
