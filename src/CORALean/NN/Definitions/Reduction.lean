module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Partition
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Layers.Operations.ActivationLayerOf
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# Reducing at many layers of one network, and [1, Thm. 1]

`ReducesAt s nn nn' f` relates `nn` to `nn'` reduced at any of its layers, indexed by the set `s`
reaching each one and the map `f` the original computes. `keep` walks a layer untouched, `merge`
reduces one sandwich via `neuronMerging_sandwich_outer`, `nil` stops: one induction, since
`Layer.enclose_not_monotone` rules out `neuronMerging_network_outer` per layer. Two *consecutive*
nonlinear layers — [1, Alg. 2] reduces every `k < κ` — need `freeze` (the merged neurons frozen at
each value `w` of the bucket's bounds and folded into layer `k+1`'s bias, as [1]'s proof of Prop. 4
does) and `widen` (the reduced layer carries the box of those biases, [1, Eq. 2]'s `W h + b ⊕ I'`).
`reducesAt_outer` and `holds_of_reducesAt` ([1, Thm. 1]) are in their own files; ℝ-only.

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]

/-- The reduced sandwich `neuronMerging_sandwich_outer` bounds `sandwich` by, trimmed to
`part.left` and boxing `part.right`'s contribution to `k+1` from `Y`. -/
noncomputable def mergedSandwich {n n₁ n₂ d r : ℕ}
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r))
    (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ} {R : Relaxation ℝ} (hR : R.IsSound σ)
    (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) (Y : Float.Interval (Vec ℝ n₁)) :
    NeuralNetwork S n n₂ :=
  .layer (LinearLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left))
    (.layer (ActivationLayer.of (n := d) hR)
      (.ofLayer (LinearWithErrorLayer.mk (W1.submatrix id part.left) b1
        (Float.Interval.mtimes (W1.submatrix id part.right)
          ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩))))


-- ========================================  MAIN TYPE  ========================================= --

/-- `nn'` is `nn` reduced at some of its layers, over the set that actually reaches each one:
`keep` skips a layer, `merge` replaces one `sandwich`, `freeze` and `widen` chain merges. -/
inductive NeuralNetwork.ReducesAt :
    ∀ {n m : ℕ}, S n → NeuralNetwork S n m → NeuralNetwork S n m →
      (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} (s : S n) {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) :
      ReducesAt s .output .output f
  | keep {n k m : ℕ} (s : S n) {L : ℕ → ℕ → Type} [inst : Enclose L S] (curr : L n k)
      {rest rest' : NeuralNetwork S k m} {g : Vec ℝ n → Vec ℝ k}
      (hg : (Enclose.toLayer (S := S) curr).Encloses g) {h : Vec ℝ k → Vec ℝ m}
      {f : Vec ℝ n → Vec ℝ m} (hf : ∀ x, f x = h (g x)) :
      ReducesAt (Enclose.enclose curr s) rest rest' h →
        ReducesAt s (.layer curr rest) (.layer curr rest') f
  -- reduces one sandwich: `part.left` survives, `part.right`'s contribution is boxed from `Y`
  | merge {n n₁ n₂ m d r : ℕ} (s : S n) (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r))
      (W0 : Mat ℝ n₁ n) (b0 : Vec ℝ n₁) {σ : ℝ → ℝ} (R : Relaxation ℝ) (hR : R.IsSound σ)
      (W1 : Mat ℝ n₂ n₁) (b1 : Vec ℝ n₂) (Y : Float.Interval (Vec ℝ n₁))
      (hY : ∀ x ∈ construct s, (fun i => σ ((W0 *ᵥ x + b0) i)) ∈ construct Y)
      {rest rest' : NeuralNetwork S n₂ m} {h : Vec ℝ n₂ → Vec ℝ m}
      {f : Vec ℝ n → Vec ℝ m}
      (hf : ∀ x, f x = h (W1 *ᵥ (fun i => σ ((W0 *ᵥ x + b0) i)) + b1)) :
      ReducesAt ((mergedSandwich part W0 b0 hR W1 b1 Y).enclose s) rest rest' h →
      ReducesAt s
        (.layer (LinearLayer.mk W0 b0) (.layer (ActivationLayer.of (n := n₁) hR)
          (.layer (LinearLayer.mk W1 b1) rest)))
        (.layer (LinearLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left))
          (.layer (ActivationLayer.of (n := d) hR)
            (.layer (LinearWithErrorLayer.mk (W1.submatrix id part.left) b1
              (Float.Interval.mtimes (W1.submatrix id part.right)
                ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)) rest')))
        f
  -- a bias known only up to `E`: the reduced layer carries the box, [1, Eq. 2]
  | widen {n n₁ m : ℕ} (s : S n) (W : Mat ℝ n₁ n) (c b : Vec ℝ n₁)
      (E : Float.Interval (Vec ℝ n₁)) (hc : c - b ∈ construct E)
      {rest rest' : NeuralNetwork S n₁ m} {h : Vec ℝ n₁ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m}
      (hf : ∀ x, f x = h (W *ᵥ x + c)) :
      ReducesAt (Enclose.enclose (LinearWithErrorLayer.mk W b E) s) rest rest' h →
      ReducesAt s (.layer (LinearLayer.mk W c) rest)
        (.layer (LinearWithErrorLayer.mk W b E) rest') f
  -- merges at `k`, then resumes at every value `w` the bucket's bounds admit
  | freeze {n n₁ n₂ m d r : ℕ} (s : S n) (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r))
      (W0 : Mat ℝ n₁ n) (c0 b0 : Vec ℝ n₁) (E0 : Float.Interval (Vec ℝ n₁))
      (hc0 : c0 - b0 ∈ construct E0) {σ : ℝ → ℝ} (R : Relaxation ℝ) (hR : R.IsSound σ)
      (W1 : Mat ℝ n₂ n₁) (c1 : Vec ℝ n₂) (Y : Float.Interval (Vec ℝ n₁))
      (hY : ∀ x ∈ construct s, (fun i => σ ((W0 *ᵥ x + c0) i)) ∈ construct Y)
      {rest : NeuralNetwork S n₂ m} {rest' : NeuralNetwork S d m}
      {h : Vec ℝ n₂ → Vec ℝ m} {f : Vec ℝ n → Vec ℝ m}
      (hf : ∀ x, f x = h (W1 *ᵥ (fun i => σ ((W0 *ᵥ x + c0) i)) + c1)) :
      -- the rest of the network, once for every value `w` of the bucket, folded into a bias
      (∀ w ∈ construct (⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ : Float.Interval (Vec ℝ r)),
        ReducesAt (Enclose.enclose (ActivationLayer.of (n := d) hR)
            (Enclose.enclose (LinearWithErrorLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left)
              ⟨E0.inf ∘ part.left, E0.sup ∘ part.left⟩) s))
          (.layer (LinearLayer.mk (W1.submatrix id part.left)
            (c1 + W1.submatrix id part.right *ᵥ w)) rest)
          rest'
          (fun z => h (W1.submatrix id part.left *ᵥ z + (c1 + W1.submatrix id part.right *ᵥ w)))) →
      ReducesAt s
        (.layer (LinearLayer.mk W0 c0) (.layer (ActivationLayer.of (n := n₁) hR)
          (.layer (LinearLayer.mk W1 c1) rest)))
        (.layer (LinearWithErrorLayer.mk (W0.submatrix part.left id) (b0 ∘ part.left)
            ⟨E0.inf ∘ part.left, E0.sup ∘ part.left⟩)
          (.layer (ActivationLayer.of (n := d) hR) rest'))
        f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
