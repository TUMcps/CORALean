import CORALean.ContSet.Interval.Real.Theorems.MtimesIsNonempty
import CORALean.Global.Partition
import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.Linear
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.Propagate

/-!
# Neuron merging: sound at every bucket

[1]'s `prop:neuron-merging`. Given output bounds `Y` for a nonlinear layer `k`
and *any* split of its neurons into survivors `B̄` and a bucket `B`, trimming
the adjacent linear layers to `B̄` and boxing what `B` would have contributed to
layer `k+1` — `W_{k+1}(·,B) · Y(B)` — soundly encloses the exact sandwich.

The bucket tolerance that picks a *good* `B` (small `W_{k+1}(·,B) · Y(B)`) never
appears: the proof below holds at every `B`, which is what makes it a heuristic
rather than a soundness hypothesis, exactly as `ConPolyZono.reduceBy_outer`
holds at every pair of partitions.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]

/-- Neuron merging (`prop:neuron-merging` in [1]): sound at *every* bucket
`part.right`, trimming layer `k-1`'s rows and layer `k+1`'s columns to the
survivors `part.left`, and boxing the bucket's contribution to `k+1` from `Y`. -/
theorem neuronMerging_sandwich_outer {n0 n n2 d r : ℕ}
    (part : Split (Fin n) into (Fin d) and (Fin r))
    (W0 : Mat ℝ n n0) (b0 : Vec ℝ n) {σ : ℝ → ℝ} (R : Relaxation σ)
    (W1 : Mat ℝ n2 n) (b1 : Vec ℝ n2) (Y : Interval (Vec ℝ n)) (X : S n0)
    (hY : ∀ x ∈ construct X, (fun i => σ ((W0 *ᵥ x + b0) i)) ∈ construct Y) :
    (NeuralNetwork.cons (Layer.linear W0 b0)
        (NeuralNetwork.cons (Layer.activation R)
          (NeuralNetwork.ofLayer (Layer.linear W1 b1)))).outputSet X
      ⊆ construct
        ((NeuralNetwork.cons (Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
            (NeuralNetwork.cons (Layer.activation R)
              (NeuralNetwork.ofLayer (Layer.linearWithError (W1.submatrix id part.left) b1
                (Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)
                (Interval.mtimes_isNonempty _ _))))).propagate X) := by
  rintro _ ⟨x, hx, rfl⟩
  set h0 : Vec ℝ n := W0 *ᵥ x + b0 with hh0
  set hk : Vec ℝ n := fun i => σ (h0 i) with hhk
  -- layer `k-1`, restricted to the survivors: rows commute with row-selection
  have hrow : ∀ i : Fin d, ((W0.submatrix part.left (id : Fin n0 → Fin n0)) *ᵥ x) i
      = (W0 *ᵥ x) (part.left i) := fun i => by
    simp [Matrix.mulVec, Matrix.submatrix_apply, dotProduct]
  have heval1 : (Layer.linear (S := S) (W0.submatrix part.left id) (b0 ∘ part.left)).eval x
      = h0 ∘ part.left := by
    funext i
    show ((W0.submatrix part.left id) *ᵥ x) i + b0 (part.left i) = h0 (part.left i)
    rw [hrow, hh0]
    rfl
  have hA1 : h0 ∘ part.left ∈ construct ((Layer.linear (W0.submatrix part.left id)
      (b0 ∘ part.left)).propagate X) :=
    heval1 ▸ (Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left)).propagate_outer X x hx
  have heval2 : (Layer.activation (S := S) R).eval (h0 ∘ part.left) = hk ∘ part.left := by
    funext i
    show σ ((h0 ∘ part.left) i) = hk (part.left i)
    rw [hhk]
    rfl
  have hA2 : hk ∘ part.left ∈ construct ((Layer.activation R).propagate
      ((Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left)).propagate X)) :=
    heval2 ▸ (Layer.activation R).propagate_outer _ _ hA1
  -- the bucket's exact output lies in `Y`, hence in `Y` restricted to the bucket
  have hB : hk ∘ part.right ∈ construct
      (⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ : Interval (Vec ℝ r)) :=
    fun i => hY x hx (part.right i)
  set s2' : S d := (Layer.activation R).propagate
      ((Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left)).propagate X) with hs2'
  set EB : Interval (Vec ℝ n2) := Interval.mtimes (W1.submatrix id part.right)
      ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ with hEB
  -- layer `k+1`'s dot product splits along the survivors and the bucket
  have hval : W1 *ᵥ hk + b1
      = (W1.submatrix id part.left) *ᵥ (hk ∘ part.left)
        + (b1 + (W1.submatrix id part.right) *ᵥ (hk ∘ part.right)) := by
    funext i
    have hsplit := part.sum_split₂ (fun j => W1 i j * hk j)
    have hl : ((W1.submatrix id part.left) *ᵥ (hk ∘ part.left)) i
        = ∑ l, W1 i (part.left l) * hk (part.left l) := by
      simp [Matrix.mulVec, Matrix.submatrix_apply, dotProduct, Function.comp]
    have hr : ((W1.submatrix id part.right) *ᵥ (hk ∘ part.right)) i
        = ∑ l, W1 i (part.right l) * hk (part.right l) := by
      simp [Matrix.mulVec, Matrix.submatrix_apply, dotProduct, Function.comp]
    show (∑ j, W1 i j * hk j) + b1 i
        = ((W1.submatrix id part.left) *ᵥ (hk ∘ part.left)) i
          + (b1 i + ((W1.submatrix id part.right) *ᵥ (hk ∘ part.right)) i)
    rw [hsplit, hl, hr]
    ring
  -- both summands are now bounded, so `mtimes_outer`/`plus_outer` apply forward
  have hAmem : (W1.submatrix id part.left) *ᵥ (hk ∘ part.left)
      ∈ construct (mtimes (𝕄 := Mat ℝ) (W1.submatrix id part.left) s2') := by
    apply mtimes_outer
    exact Set.mem_biUnion rfl (Set.mem_image_of_mem _ hA2)
  have hEBmem : (W1.submatrix id part.right) *ᵥ (hk ∘ part.right) ∈ construct EB :=
    Interval.mtimes_outer (W1.submatrix id part.right)
      ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ (Set.mem_image_of_mem _ hB)
  have hBoxmem : b1 + (W1.submatrix id part.right) *ᵥ (hk ∘ part.right)
      ∈ construct (Interval.plus (Interval.point b1) EB) :=
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b1) hEBmem)
  show W1 *ᵥ hk + b1 ∈ construct
      (plus (mtimes (𝕄 := Mat ℝ) (W1.submatrix id part.left) s2')
        (ofInterval (Interval.plus (Interval.point b1) EB)))
  rw [hval]
  exact plus_outer _ _ (Set.add_mem_add hAmem (ofInterval_outer _ hBoxmem))

end CORALean.Real
