import CORALean.NN.Theorems.Misclassified
import CORALean.NN.Theorems.NeuronMergingNetworkOuter
import CORALean.NN.Theorems.OutputSetSubset
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanation
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Transfer: sufficient for the abstract network is sufficient for the original

`col:suff-nn-suff-nnabs` [1]: a sufficient explanation of `nnAbs` is one of `nn`,
given that `nnAbs`'s propagated enclosure of `explainBox` contains `nn`'s exact
image there. The hypothesis `hcontain` is what an abstraction owes, and the two
corollaries are the networks the refinement loop [1, Alg. 2] actually visits: a
neuron-merged one, where `neuronMerging_network_outer` [2] supplies it, and — at
the loop's last step, reduction rate `1` — the original network, where
`outputSet_subset` does.

Set-level throughout, so there is no float counterpart here, exactly as for
`neuronMerging_network_outer`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.neuronMerging_network_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus Mtimes IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}

/-- Transfer (`col:suff-nn-suff-nnabs` [1]): sufficient for `nnAbs` is sufficient
for `nn`, given that `nnAbs`'s enclosure of `explainBox` contains `nn`'s exact
image there. -/
theorem NeuralNetwork.suffExplanation_of_abstract (nn nnAbs : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hcontain : nn.outputSet (ofInterval (explainBox x ε E))
      ⊆ construct (nnAbs.propagate (ofInterval (explainBox x ε E))))
    (hsuffAbs : nnAbs.IsSuffExplanationAbstract x ε E l) :
    nn.IsSuffExplanation x ε E l := by
  have hspec : (Specification.unsafeSet (misclassified m l)).Holds
      (nn.outputSet (ofInterval (explainBox x ε E))) :=
    (Specification.unsafeSet (misclassified m l)).holds_of_outer hcontain hsuffAbs
  intro x' hx' j hj
  have hmem : nn.eval x' ∈ nn.outputSet (ofInterval (explainBox x ε E)) :=
    ⟨x', ofInterval_outer _ hx', rfl⟩
  have hd := Set.disjoint_left.mp hspec hmem
  by_contra hc
  exact hd ⟨j, hj, not_lt.mp hc⟩

/-- Transfer at a network the abstraction actually produces: merging the bucket
`part.right` at one layer, `hcontain` is `neuronMerging_network_outer` [2] and
nothing further is assumed. -/
theorem NeuralNetwork.suffExplanation_of_neuronMerging [∀ n, Plus (S n) (Vec ℝ n)]
    [Mtimes (Mat ℝ) S] [IntervalOuter S] {n₀ n₁ nk n₂ n₃ d r : ℕ}
    (pre : NeuralNetwork S n₀ n₁) (post : NeuralNetwork S n₂ n₃)
    (part : Split (Fin nk) into (Fin d) and (Fin r))
    (W0 : Mat ℝ nk n₁) (b0 : Vec ℝ nk) {σ : ℝ → ℝ} (R : Relaxation σ)
    (W1 : Mat ℝ n₂ nk) (b1 : Vec ℝ n₂) (Y : Interval (Vec ℝ nk))
    (x : Vec ℝ n₀) (ε : ℝ) (E : Finset (Fin n₀)) (l : Fin n₃)
    (hY : ∀ z ∈ construct (pre.propagate (ofInterval (explainBox x ε E))),
      (fun i => σ ((W0 *ᵥ z + b0) i)) ∈ construct Y)
    -- the reduced network: both linear layers trimmed to `part.left`, the bucket boxed into `k+1`
    (hsuffAbs : (NeuralNetwork.cons pre.toLayer
        (.cons (Layer.linear (W0.submatrix part.left id) (b0 ∘ part.left))
          (.cons (Layer.activation R)
            (.cons (Layer.linearWithError (W1.submatrix id part.left) b1
                (Interval.mtimes (W1.submatrix id part.right)
                  ⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩)
                (Interval.mtimes_isNonempty _ _))
              post)))).IsSuffExplanationAbstract x ε E l) :
    -- and the original, whose exact image `neuronMerging_network_outer` puts inside it
    (NeuralNetwork.cons pre.toLayer
        (.cons (Layer.linear W0 b0)
          (.cons (Layer.activation R)
            (.cons (Layer.linear W1 b1) post)))).IsSuffExplanation x ε E l :=
  NeuralNetwork.suffExplanation_of_abstract _ _ x ε E l
    (neuronMerging_network_outer pre post part W0 b0 R W1 b1 Y
      (ofInterval (explainBox x ε E)) hY) hsuffAbs

/-- Transfer at the loop's fixed point, where the abstraction is `nn` itself:
separation on `nn`'s own propagated set is sufficiency for `nn` outright. -/
theorem NeuralNetwork.suffExplanation_of_propagate (nn : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hsuffAbs : nn.IsSuffExplanationAbstract x ε E l) :
    nn.IsSuffExplanation x ε E l :=
  nn.suffExplanation_of_abstract nn x ε E l (nn.outputSet_subset _) hsuffAbs

end CORALean.Real
