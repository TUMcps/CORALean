import CORALean.NN.Theorems.OutputSetSubset
import CORALean.NN.Theorems.SuffExplanationTransfer

/-!
# Transfer at the loop's fixed point

Split out of `SuffExplanationTransfer.lean` (issue #62): one of the two
corollaries the refinement loop [1, Alg. 2] actually visits, alongside
`SuffExplanationOfNeuronMerging.lean` — at the loop's last step, reduction
rate `1`, the abstraction is `nn` itself, and separation on `nn`'s own
propagated set is sufficiency for `nn` outright.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.suffExplanation_of_propagate (nn : NeuralNetwork S n m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m)
    (hsuffAbs : nn.IsSuffExplanationAbstract x ε E l) :
    nn.IsSuffExplanation x ε E l :=
  nn.suffExplanation_of_abstract nn x ε E l (nn.outputSet_subset _) hsuffAbs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
