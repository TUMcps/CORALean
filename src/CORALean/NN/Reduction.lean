import CORALean.ContSet.Interval.Real.Theorems.MtimesIsNonempty
import CORALean.Global.Partition
import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.Linear
import CORALean.NN.Operations.Enclose

/-!
# Reducing at many layers of one network, and [1, Thm. 1]

`ReducesAt s nn nn' f` relates `nn` to `nn'` reduced at any of its layers, indexed by the set
`s` that actually reaches each one and by the map `f` the original computes — `merge` is sound
only at the sandwich's own map, which `Layer` no longer stores. `keep` walks a layer untouched,
`merge` reduces one sandwich via `neuronMerging_sandwich_outer`, `nil` stops — several `merge`s
in one derivation reduce at several layers. One induction, not
`neuronMerging_network_outer` applied per layer:
`Layer.enclose_not_monotone` rules that out.

`reducesAt_outer` (soundness) and `holds_of_reducesAt` ([1, Thm. 1]) are in their own files.
Choosing *where* to reduce — Alg. 2 — owes no proof: this holds at every derivation.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]

/-- The unreduced sandwich a `merge` step replaces: linear, activation, linear. -/
def sandwich {n n₁ n₂ : ℕ} (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ} (R : Real.Relaxation σ)
    (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) : NeuralNetwork S n n₂ :=
  .cons (Real.Layer.linear W0 b0)
    (.cons (Real.Layer.activation R) (.ofLayer (Real.Layer.linear W1 b1)))

/-- The reduced sandwich `neuronMerging_sandwich_outer` bounds `sandwich` by, trimmed to
`part.left` and boxing `part.right`'s contribution to `k+1` from `Y`. -/
noncomputable def mergedSandwich {n n₁ n₂ d r : ℕ}
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r))
    (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ} (R : Real.Relaxation σ)
    (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) (Y : Real.Interval (Vec ℝ n₁)) : NeuralNetwork S n n₂ :=
  .cons (Real.Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
    (.cons (Real.Layer.activation R)
      (.ofLayer (Real.Layer.linearWithError (W1.submatrix id part.left) b1
        (Real.Interval.mtimes (W1.submatrix id part.right)
          ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩))))


-- ========================================  MAIN TYPE  ========================================= --

/-- `nn'` is `nn` reduced at some of its layers, over the set that actually reaches each one:
`keep` skips a layer, `merge` replaces one `sandwich` by its `mergedSandwich`, `nil` stops. -/
inductive NeuralNetwork.ReducesAt :
    ∀ {n m : ℕ}, S n → NeuralNetwork S n m → NeuralNetwork S n m →
      (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} (s : S n) {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) :
      ReducesAt s .nil .nil f
  | keep {n k m : ℕ} (s : S n) (L : Layer S n k) {rest rest' : NeuralNetwork S k m}
      {g : Vec ℝ n → Vec ℝ k} (hg : L.Sound g) {h : Vec ℝ k → Vec ℝ m}
      {f : Vec ℝ n → Vec ℝ m} (hf : ∀ x, f x = h (g x)) :
      ReducesAt (L.enclose s) rest rest' h → ReducesAt s (.cons L rest) (.cons L rest') f
  -- reduces one sandwich: `part.left` survives, `part.right`'s contribution is boxed from `Y`
  | merge {n n₁ n₂ m d r : ℕ} (s : S n) (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r))
      (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ} (R : Real.Relaxation σ)
      (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) (Y : Real.Interval (Vec ℝ n₁))
      (hY : ∀ x ∈ construct s, (fun i => σ ((W0 *ᵥ x + b0) i)) ∈ construct Y)
      {rest rest' : NeuralNetwork S n₂ m} {h : Vec ℝ n₂ → Vec ℝ m}
      {f : Vec ℝ n → Vec ℝ m}
      (hf : ∀ x, f x = h (W1 *ᵥ (fun i => σ ((W0 *ᵥ x + b0) i)) + b1)) :
      ReducesAt ((mergedSandwich part W0 b0 R W1 b1 Y).enclose s) rest rest' h →
      ReducesAt s
        (.cons (Real.Layer.linear W0 b0) (.cons (Real.Layer.activation R)
          (.cons (Real.Layer.linear W1 b1) rest)))
        (.cons (Real.Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
          (.cons (Real.Layer.activation R)
            (.cons (Real.Layer.linearWithError (W1.submatrix id part.left) b1
              (Real.Interval.mtimes (W1.submatrix id part.right)
                ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)) rest')))
        f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
