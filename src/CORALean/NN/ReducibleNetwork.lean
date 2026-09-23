import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.Linear
import CORALean.NN.MergeBucket
import CORALean.NN.NeuralNetwork

/-!
# A network in the form [1, Alg. 2] reads and writes

[1, Def. 1]'s alternating network, read two layers at a time — the linear layer `k-1`, then the
nonlinear layer `k`, for `k = 2, 4, …, κ` — which is exactly the stride of [1, Alg. 2]'s loop.
Each linear layer is in [1, Eq. 2]'s form `W h + b ⊕ I'`: an original network has `I' = [0, 0]`,
and a reduced one carries there what merging cost it. So [1, Alg. 2]'s input and output are
one type, which is what [1, Alg. 3] needs: it runs [1, Alg. 2] on a network already reduced.

Each nonlinear layer stores its relaxation and where its merge buckets are initialised.

`toNetwork` is the network of layers [1, Eq. 2] denotes, the box an added error. `Instance`
is one network it stands for: every `I'` replaced by a value `c - b` in it, the layers plain.
An original network, `I' = [0, 0]`, has exactly one instance, itself.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


/-- [1, Eq. 2]'s linear layer, `W h + b ⊕ I'`: the weights, the bias, and the box of errors
merging has added to its output. -/
structure ReducedLinear (n m : ℕ) where
  W : Mat ℝ m n
  b : Vec ℝ m
  I' : Interval (Vec ℝ m)

/-- The layer [1, Eq. 2] names, `W h + b ⊕ I'`. -/
def ReducedLinear.toLayer {n m : ℕ} (L : ReducedLinear n m) : Layer S n m :=
  Layer.linearWithError L.W L.b L.I'


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1] two layers at a time, the linear one in [1, Eq. 2]'s form `W h + b ⊕ I'`. -/
inductive ReducibleNetwork : ℕ → ℕ → Type where
  | nil {n : ℕ} : ReducibleNetwork n n
  | cons {n n₁ m : ℕ} (L : ReducedLinear n n₁) {σ : ℝ → ℝ} (R : Relaxation σ)
      (B : MergeBuckets ℝ) (rest : ReducibleNetwork n₁ m) : ReducibleNetwork n m

/-- The layers [1, Eq. 2] names: `W h + b ⊕ I'`, then the activation. -/
def ReducibleNetwork.toNetwork : ∀ {n m : ℕ}, ReducibleNetwork n m → NeuralNetwork S n m
  | _, _, .nil => .nil
  | _, _, .cons L R _ rest => .cons L.toLayer (.cons (Layer.activation R) rest.toNetwork)

/-- `nn` is `Φ` with every error box replaced by one of its values, and computes `f`. -/
inductive ReducibleNetwork.Instance :
    ∀ {n m : ℕ}, ReducibleNetwork n m → NeuralNetwork S n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) : Instance .nil .nil f
  | cons {n n₁ m : ℕ} {L : ReducedLinear n n₁} {c : Vec ℝ n₁} {σ : ℝ → ℝ} {R : Relaxation σ}
      {B : MergeBuckets ℝ} {rest : ReducibleNetwork n₁ m} {nn : NeuralNetwork S n₁ m}
      {h : Vec ℝ n₁ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m}
      (hc : c - L.b ∈ construct L.I') (hrest : Instance rest nn h)
      (hf : ∀ x, f x = h (fun i => σ ((L.W *ᵥ x + c) i))) :
      Instance (.cons L R B rest) (.cons (Layer.linear L.W c) (.cons (Layer.activation R) nn)) f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
