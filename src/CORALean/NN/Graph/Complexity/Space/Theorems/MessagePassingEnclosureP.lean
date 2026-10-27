module

public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `GNN.messagePassingEnclosure`'s counts

[1, Prop. 4]'s `O(h³)` as the count itself: two `bilin`s over the `m + N` shared factors leave `𝒫`
with `((m+N+1)² + 1)(m+N+1)` dependent generators and no independent ones, `rfl` against the
structure instances. Cubic in `m + N` where [1] is cubic in the edge count alone:
`aux_sqrtBroadcast` spends a residual factor on *every* node.

`messagePassingEnclosure_h_le` is the form [1, Thm. 1] composes; `messagePassingEnclosure_h_isBigO`
is [1, Prop. 4] in `O` notation, along a family of edge sets growing with `m`.

## Inputs
* `R` – relaxation of the square root
* `A` – adjacency matrix
* `U` – uncertain edges

## Hypotheses
* none

## Conclusion
* the enclosure has m + N factors

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `messagePassingEnclosure`'s result. -/
theorem GNN.messagePassingEnclosure_p (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : (GNN.messagePassingEnclosure R A U).p = m + N := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
