import CORALean.NN.NeuralNetwork

/-!
# Propagating a set through the graph

The whole verification pipeline, one line per constructor: hand the input set
to the first layer and the result to the rest. No layer sees anything but a
set of the representation, so nothing here knows which representation that is
or which layers these are.

Precision is entirely the layers' business: a representation that loses
nothing at a linear layer and plenty at an activation encloses exactly that.

[1, Def. 7]'s abstract network is this recursion, read at whichever
representation and layers a caller supplies: `H'_0` is `output`'s case, the
input handed back untouched, and `H'_k := L'_k(H'_{k-1})` is `layer`'s. The
paper's own `L'_k` — an affine map, Minkowski-summed with an error box, then
an elementwise `σ` — is one instance among the layers `NN/Layers/` builds,
not what this definition is tied to. [2, Alg. 1]'s own per-layer loop is
another, at whichever layer `ActivationPoly.lean` builds.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.enclose : ∀ {n m : ℕ}, NeuralNetwork S n m → S n → S m
  | _, _, .output, s => s
  | _, _, .layer (inst := _) curr tail, s => tail.enclose (Enclose.enclose curr s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
