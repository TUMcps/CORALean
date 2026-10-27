module

public import CORALean.NN.Graph.Definitions.IsPermInvariant
public import CORALean.NN.Graph.Operations.SumPoolLin

@[expose] public section

/-!
# Summation pooling is permutation invariant

[1, Def. 5]'s condition at Eq. (1)'s aggregation, the sum across the nodes: a permutation of
the rows reindexes each feature's sum and leaves it unchanged.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* summation pooling is a permutation-invariant aggregation

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 5]: `sumPoolLin` is a permutation-invariant aggregation. -/
theorem GNN.sumPoolLin_isPermInvariant : GNN.IsPermInvariant (GNN.sumPoolLin N F) := by
  intro σ H
  funext j
  exact Equiv.sum_comp σ (fun i => H i j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
