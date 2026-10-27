module

public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnActStepsHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureP
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHIsBigO
public import CORALean.NN.Graph.Operations.Alg1Node

@[expose] public section

/-!
# `Alg. 1`'s count for a node-level output

[1, Thm. 1 (generators)]: the message passing `P` has `O(m³)` generators in the `m` uncertain edges
(`messagePassingEnclosure_h_le`), each of the `κ'` steps multiplies the count by at most
`P.h + 2` and adds the activation's neurons (`gcnActSteps_h_le`), and the input's `h_x` generators
are its dependent and independent ones. So `κ'` steps leave at most
`K^κ' m^(3κ') (h_x + 1 + κ' ν)` generators, `K` collecting the graph size and `ν = |N| c_max`
the neurons an activation adds.

## Inputs
* `R` – relaxation of the activations
* `A` – adjacency matrix
* `U` – uncertain edges
* `L` – number of graph layers
* `c` – layer widths
* `W` – graph layer weights
* `acts` – activation layers
* `X` – input polynomial zonotope

## Hypotheses
* none

## Conclusion
* the node-level enclosure equals the chain of activation steps on the padded message passing

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Alg. 1` on the graph layers is `gcnActSteps` at the message passing padded against the
dependent form of `X`. -/
theorem GNN.alg1Node_eq_gcnActSteps (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (L : ℕ) (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
    (acts : ∀ s, GNN.ActLayer N (c (s + 1))) (X : PolyZonotope (Mat ℝ N (c 0))) :
    GNN.alg1Node R A U L c W acts X
      = GNN.gcnActSteps L c W acts ((GNN.messagePassingEnclosure R A U).padBack X.dependent.p)
          (X.dependent.padFront (GNN.messagePassingEnclosure R A U).p) rfl := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
