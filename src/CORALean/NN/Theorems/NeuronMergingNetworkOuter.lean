import CORALean.NN.Operations.ToLayer
import CORALean.NN.Theorems.NeuronMergingOuter

/-!
# A merge at one layer of a whole network

`neuronMerging_sandwich_outer` is stated over the three layers a merge touches,
because those are the three it changes. A merge is applied at a layer *inside* a
network, though, and this is that statement: the same sandwich between an
arbitrary prefix and an arbitrary suffix, which is the containment
`NeuralNetwork.suffExplanation_of_abstract` [2] takes as its hypothesis.

Neither side of the sandwich is assumed anything of. The prefix contributes only
its own enclosure, which every network has, and so the bounds `Y` are asked for
only at the points the prefix actually reaches. The suffix is applied to a set on
both sides, so nothing about it has to be re-proved — which is why the reduction
composes with the rest of the network for free and merges at two *distant*
layers compose by applying this twice.

Merges two nonlinear layers apart do not: they share the linear layer between
them, one trimming its rows and the other its columns, so they are not two
instances of this theorem.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
* [2] `CORALean.Real.NeuralNetwork.suffExplanation_of_abstract`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Neuron merging, [1, Prop. 4], at a layer of any network: the
merged sandwich sits between `pre` and `post`, and `Y` is only ever asked to
bound the nonlinear layer over what `pre` reaches. -/
theorem neuronMerging_network_outer {n₀ n₁ n n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin n) into (Fin d) and (Fin r))
    (W0 : Mat ℝ n n₁) (b0 : Vec ℝ n) {σ : ℝ → ℝ} (R : Relaxation σ)
    (W1 : Mat ℝ n₂ n) (b1 : Vec ℝ n₂) (Y : Interval (Vec ℝ n)) (X : S n₀)
    (hY : ∀ x ∈ construct (pre.propagate X),
      (fun i => σ ((W0 *ᵥ x + b0) i)) ∈ construct Y) :
    (NeuralNetwork.cons pre.toLayer
        (.cons (Layer.linear W0 b0)
          (.cons (Layer.activation R)
            (.cons (Layer.linear W1 b1) post)))).outputSet X
      ⊆ construct ((NeuralNetwork.cons pre.toLayer
          (.cons (Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
            (.cons (Layer.activation R)
              (.cons (Layer.linearWithError (W1.submatrix id part.left) b1
                  (Interval.mtimes (W1.submatrix id part.right)
                    ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)
                  (Interval.mtimes_isNonempty _ _))
                post)))).propagate X) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the prefix hands the sandwich a set, and that set is what `hY` is stated over
  have hpre : pre.eval x ∈ construct (pre.propagate X) := pre.propagate_outer X x hx
  have hmid := neuronMerging_sandwich_outer part W0 b0 R W1 b1 Y (pre.propagate X) hY
    ⟨pre.eval x, hpre, rfl⟩
  -- the suffix is unchanged, so its own obligation carries the point the rest of the way
  exact post.propagate_outer _ _ hmid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
