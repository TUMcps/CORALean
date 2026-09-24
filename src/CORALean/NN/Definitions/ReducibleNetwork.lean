import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Definitions.MergeBucket
import CORALean.NN.NeuralNetwork

/-!
# A network in the form [1, Alg. 2] reads and writes

[1, Def. 1]'s alternating network, read two layers at a time — the linear layer `k-1`, then the
nonlinear layer `k`, for `k = 2, 4, …, κ` — which is exactly the stride of [1, Alg. 2]'s loop.
Each linear layer is in [1, Eq. 2]'s form `W h + b ⊕ I'`, stored in the scalar `𝕋`: an original
network has `I' = [0, 0]`, a reduced one carries there what merging cost it. So [1, Alg. 2]'s
input and output are one type, which is what [1, Alg. 3] needs. Each nonlinear layer stores its
relaxation and where its merge buckets are initialised.

`Instance` is what `Φ` stands for: a map built from the exact affine maps the stored scalars
denote, every error box at one real value `c - b` in it, and every activation a `σ` its
relaxation is sound for. `InstanceNetwork` is the same at `𝕋 := ℝ`, naming the network of
layers each instance is, which is what `ReducesAt` relates; an instance's bias is real, so no
other scalar can store it.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]

/-- [1, Eq. 2]'s linear layer, `W h + b ⊕ I'`: the weights, the bias, and the box of errors
merging has added to its output. -/
structure ReducedLinear (𝕋 : Type) (n m : ℕ) where
  W : Mat 𝕋 m n
  b : Vec 𝕋 m
  I' : Float.Interval 𝕋 m


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1] two layers at a time, the linear one in [1, Eq. 2]'s form `W h + b ⊕ I'`. -/
inductive ReducibleNetwork (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] :
    ℕ → ℕ → Type where
  | nil {n : ℕ} : ReducibleNetwork 𝕋 n n
  | cons {n n₁ m : ℕ} (L : ReducedLinear 𝕋 n n₁) (R : Relaxation 𝕋) (B : MergeBuckets 𝕋)
      (rest : ReducibleNetwork 𝕋 n₁ m) : ReducibleNetwork 𝕋 n m

/-- `f` is what `Φ` computes with every error box at one of its values and every activation
a `σ` its relaxation is sound for. -/
inductive ReducibleNetwork.Instance :
    ∀ {n m : ℕ}, ReducibleNetwork 𝕋 n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) : Instance .nil f
  | cons {n n₁ m : ℕ} {L : ReducedLinear 𝕋 n n₁} {c : Vec ℝ n₁} {R : Relaxation 𝕋}
      {σ : ℝ → ℝ} {B : MergeBuckets 𝕋} {rest : ReducibleNetwork 𝕋 n₁ m}
      {h : Vec ℝ n₁ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m} (hR : R.Sound σ)
      (hc : c - Float.toRealVec L.b ∈ L.I'.construct) (hrest : Instance rest h)
      (hf : ∀ x, f x = h (fun i => σ ((Float.toRealMat L.W *ᵥ x + c) i))) :
      Instance (.cons L R B rest) f

/-- ℝ-only, an instance's bias `c` being real: `nn` is `Φ` with every error box replaced by
one of its values, as a network of layers, and computes `f`. -/
inductive ReducibleNetwork.InstanceNetwork {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] :
    ∀ {n m : ℕ}, ReducibleNetwork ℝ n m → NeuralNetwork S n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) : InstanceNetwork .nil .nil f
  | cons {n n₁ m : ℕ} {L : ReducedLinear ℝ n n₁} {c : Vec ℝ n₁} {R : Relaxation ℝ}
      {σ : ℝ → ℝ} {B : MergeBuckets ℝ} {rest : ReducibleNetwork ℝ n₁ m}
      {nn : NeuralNetwork S n₁ m} {h : Vec ℝ n₁ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m}
      (hR : R.Sound σ) (hc : c - L.b ∈ L.I'.construct) (hrest : InstanceNetwork rest nn h)
      (hf : ∀ x, f x = h (fun i => σ ((L.W *ᵥ x + c) i))) :
      InstanceNetwork (.cons L R B rest)
        (.cons (Layer.linear L.W c) (.cons (Layer.activation R) nn)) f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
