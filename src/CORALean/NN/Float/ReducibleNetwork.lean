import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.MergeBucket
import CORALean.NN.NeuralNetwork

/-!
# A network in the form [1, Alg. 2] reads and writes, over a floating-point scalar

`Real.ReducibleNetwork` with weights, biases, error boxes and relaxations stored as floats:
[1, Def. 1] two layers at a time, the linear one in [1, Eq. 2]'s form `W h + b ⊕ I'`.

`Instance` is what such a network computes, and the one place `ℝ` enters: a map `f` built from
the exact affine maps the stored floats denote, every error box at one real value `c - b` in
it, and every activation a `σ` its relaxation is sound for. It names no network of layers, as
the exact layer's does: an instance's bias is real, and a float layer cannot store it.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]

/-- [1, Eq. 2]'s linear layer `W h + b ⊕ I'`, stored as floats. -/
structure ReducedLinear (𝕋 : Type) (n m : ℕ) where
  W : Mat 𝕋 m n
  b : Vec 𝕋 m
  I' : Interval 𝕋 m

/-- The layer [1, Eq. 2] names, `W h + b ⊕ I'`. -/
def ReducedLinear.toLayer {n m : ℕ} (L : ReducedLinear 𝕋 n m) : Layer S n m :=
  Layer.linearWithError L.W L.b L.I'


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1] two layers at a time, the linear one in [1, Eq. 2]'s form, in floats. -/
inductive ReducibleNetwork (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] :
    ℕ → ℕ → Type where
  | nil {n : ℕ} : ReducibleNetwork 𝕋 n n
  | cons {n n₁ m : ℕ} (L : ReducedLinear 𝕋 n n₁) (R : Relaxation 𝕋) (B : MergeBuckets 𝕋)
      (rest : ReducibleNetwork 𝕋 n₁ m) : ReducibleNetwork 𝕋 n m

/-- The layers [1, Eq. 2] names: `W h + b ⊕ I'`, then the activation. -/
def ReducibleNetwork.toNetwork : ∀ {n m : ℕ}, ReducibleNetwork 𝕋 n m → NeuralNetwork S n m
  | _, _, .nil => .nil
  | _, _, .cons L R _ rest => .cons L.toLayer (.cons (Layer.activation R) rest.toNetwork)

/-- `f` is what `Φ` computes with every error box at one of its values and every activation
a `σ` its relaxation is sound for. -/
inductive ReducibleNetwork.Instance :
    ∀ {n m : ℕ}, ReducibleNetwork 𝕋 n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) : Instance .nil f
  | cons {n n₁ m : ℕ} {L : ReducedLinear 𝕋 n n₁} {c : Vec ℝ n₁} {R : Relaxation 𝕋}
      {σ : ℝ → ℝ} {B : MergeBuckets 𝕋} {rest : ReducibleNetwork 𝕋 n₁ m}
      {h : Vec ℝ n₁ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m} (hR : R.Sound σ)
      (hc : c - toRealVec L.b ∈ L.I'.construct) (hrest : Instance rest h)
      (hf : ∀ x, f x = h (fun i => σ ((toRealMat L.W *ᵥ x + c) i))) :
      Instance (.cons L R B rest) f

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
