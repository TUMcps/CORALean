import CORALean.ContSet.Interval.Float.Theorems.NonemptyHullIsNonempty
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.NN.Layers.Definitions.ActivationLayer
import CORALean.NN.Layers.Definitions.ActivationPolyLayer
import CORALean.NN.Layers.Definitions.AvgPoolLayer
import CORALean.NN.Layers.Definitions.BatchNormLayer
import CORALean.NN.Layers.Definitions.ConvLayer
import CORALean.NN.Layers.Definitions.IdentityLayer
import CORALean.NN.Layers.Definitions.LinearLayer
import CORALean.NN.Layers.Definitions.LinearWithErrorLayer
import CORALean.NN.Layers.Definitions.MaxPoolLayer
import CORALean.NN.Layers.Definitions.ReluLayer
import CORALean.NN.Layers.Definitions.ReshapeLayer
import CORALean.NN.Layers.Definitions.SigmoidLayer
import CORALean.NN.Layers.Definitions.SigmoidPolyLayer
import CORALean.NN.Layers.Definitions.SoundLayer
import CORALean.NN.Layers.Definitions.SoftmaxLayer
import CORALean.NN.Layers.Definitions.TanhLayer
import CORALean.NN.Layers.Theorems.ActivationPolySound
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.AvgPoolSound
import CORALean.NN.Layers.Theorems.BatchNormSound
import CORALean.NN.Layers.Theorems.ConvSound
import CORALean.NN.Layers.Theorems.LinearSound
import CORALean.NN.Layers.Theorems.LinearWithErrorSound
import CORALean.NN.Layers.Theorems.MaxPoolSound
import CORALean.NN.Layers.Theorems.ReluSound
import CORALean.NN.Layers.Theorems.ReshapeSound
import CORALean.NN.Layers.Theorems.SigmoidPolySound
import CORALean.NN.Layers.Theorems.SigmoidSound
import CORALean.NN.Layers.Theorems.SoftmaxSound
import CORALean.NN.Layers.Theorems.TanhSound

/-!
# Every standard layer kind, as an `Enclose` instance

Each instance is the kind's layer in `Operations/`, the function its theorem in `Theorems/`
names as `eval`, and that theorem as `enclose_outer`: nothing is proved here that was not
proved of the layer already. Written once over the scalar, so each is the kind at `ℝ` and at
every machine scalar alike, and each asks of the set only the operations its layer calls.

A kind that keeps the dimension matches on its `dim` to learn the two dimensions agree,
which is a cast the compiler erases.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

/-- `Layer.linear`, at the affine map the weights denote. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] :
    Enclose (LinearLayer 𝕋) S where
  eval l := Erased.mk fun x => toRealMat l.W *ᵥ x + toRealVec l.b
  enclose l := (Layer.linear (S := S) l.W l.b).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.linear_sound l.W l.b).image_subset s

/-- `Layer.linearWithError` at the box's nonempty hull, committing to its centre. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] :
    Enclose (LinearWithErrorLayer 𝕋) S where
  eval l := Erased.mk fun x =>
    toRealMat l.W *ᵥ x + toRealVec l.b + l.E.nonemptyHull.nominal.center
  enclose l := (Layer.linearWithError (S := S) l.W l.b l.E.nonemptyHull).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.linearWithError_sound l.W l.b _ l.E.nonemptyHull_isNonempty).image_subset s

/-- `Layer.relu`, at `relu` coordinatewise. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋]
    [Float.OfInterval S 𝕋] : Enclose (ReluLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.relu (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨lam, rfl⟩ => (Layer.relu (S := S) lam).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨lam, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.relu_sound lam).image_subset s

/-- `Layer.sigmoid`, at the sigmoid coordinatewise. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋]
    [Float.OfInterval S 𝕋] : Enclose (SigmoidLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.sigmoid (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨k, rfl⟩ => (Layer.sigmoid (𝕋 := 𝕋) (S := S) k).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.sigmoid_sound k).image_subset s

/-- `Layer.tanh`, at `tanh` coordinatewise. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋]
    [Float.OfInterval S 𝕋] : Enclose (TanhLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, rfl⟩ => Erased.mk fun x i => Real.tanh (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨k, rfl⟩ => (Layer.tanh (𝕋 := 𝕋) (S := S) k).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.tanh_sound k).image_subset s

/-- `Layer.softmax`, asking of the set only the two boxes. -/
instance [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] : Enclose (SoftmaxLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, rfl⟩ => Erased.mk Real.softmax
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨k, rfl⟩ => (Layer.softmax (𝕋 := 𝕋) (S := S) k).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨k, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.softmax_sound (𝕋 := 𝕋) k).image_subset s

/-- `Layer.activation`, at the `σ` the weights' proof names. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋]
    [Float.OfInterval S 𝕋] : Enclose (ActivationLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, hR, rfl⟩ => Erased.mk fun x i => hR.choose (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨R, _, rfl⟩ => (Layer.activation (S := S) R).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨_, hR, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.activation_sound hR.choose_spec).image_subset s

/-- `Layer.batchNorm`, each coordinate scaled and shifted by its channel. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] :
    Enclose (BatchNormLayer 𝕋) S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ =>
      Erased.mk fun x i => toReal (scale (chan i)) * x i + toReal (shift (chan i))
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ => (Layer.batchNorm (S := S) chan scale shift).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨_, chan, scale, shift, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.batchNorm_sound chan scale shift).image_subset s

/-- `Layer.conv`, the stencil read as a sum. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] :
    Enclose (ConvLayer 𝕋) S where
  eval l := Erased.mk fun x j => (∑ i, toReal (l.K (l.chan j) i) * x (l.tap j i)) + toReal (l.b j)
  enclose l := (Layer.conv (S := S) l.chan l.tap l.K l.b).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.conv_sound l.chan l.tap l.K l.b l.tap_injective).image_subset s

/-- `Layer.avgPool`, the window sum scaled by the stored reciprocal. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] :
    Enclose (AvgPoolLayer 𝕋) S where
  eval l := Erased.mk fun x j => toReal l.winv * ∑ i, x (l.tap j i)
  enclose l := (Layer.avgPool (S := S) l.winv l.tap).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.avgPool_sound l.winv l.tap l.tap_injective).image_subset s

/-- `Layer.maxPool`, at each window's maximum. -/
instance [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋]
    [Float.OfInterval S 𝕋] : Enclose (MaxPoolLayer 𝕋) S where
  eval l := Erased.mk fun x j => Real.windowMax fun i => x (l.tap j i)
  enclose l := (Layer.maxPool (S := S) l.tap l.pivot).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.maxPool_sound l.tap l.pivot).image_subset s

/-- `Layer.reshape`, asking of the set only `Reindex`. -/
instance [Reindex S] : Enclose ReshapeLayer S where
  eval l := Erased.mk (reindexLin l.e)
  enclose l := (Layer.reshape (S := S) l.e).enclose
  enclose_outer l s := by
    rw [Erased.out_mk]
    exact (Layer.reshape_sound l.e).image_subset s

/-- `Layer.identity`, asking of the set nothing at all. -/
instance : Enclose IdentityLayer S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨rfl⟩ => Erased.mk id
  enclose := fun {n m} l => match n, m, l with
    | k, _, ⟨rfl⟩ => (Layer.identity S k).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨rfl⟩ => by
      rw [Erased.out_mk]
      exact Layer.identity_sound.image_subset s

/-- `Layer.sigmoidPoly`, at a polynomial zonotope. -/
instance : Enclose (SigmoidPolyLayer 𝕋) (Float.PolyZonotope 𝕋) where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, _, _, _, _, _, rfl⟩ => Erased.mk fun x i => Real.sigmoid (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨k, _, _, c, dx, p, rfl⟩ => (Layer.sigmoidPoly k c dx p).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨k, _, _, c, dx, p, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.sigmoidPoly_sound k c dx p).image_subset s

/-- `Layer.activationPoly`, at a polynomial zonotope. -/
instance : Enclose (ActivationPolyLayer 𝕋) (Float.PolyZonotope 𝕋) where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨_, _, hP, rfl⟩ => Erased.mk fun x i => hP.choose (x i)
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨_, P, _, rfl⟩ => (Layer.activationPoly P).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨_, _, hP, rfl⟩ => by
      rw [Erased.out_mk]
      exact (Layer.activationPoly_sound hP.choose_spec).image_subset s

/-- A packed layer, its three fields read back. -/
instance : Enclose (SoundLayer S) S where
  eval l := l.eval
  enclose l := l.enclose
  enclose_outer l := l.enclose_outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
