import CORALean.ContDynamics.NeurNetContrSysDT.Cost.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Cost.ReachBound

/-!
# What running `NeurNetContrSysDT.reach` costs

`Reach.lean` says which operations a step runs and at what sizes, mirroring
`Operations.lean`'s alternation line for line: one `NeuralNetwork.encloseCost`
and one `LinearSysDT` step, at `𝒵`. `ReachBound.lean` proves the run's cost is
at most `k` worst-case steps, out of the per-operation counts in
`ContSet/Zonotope/Real/Cost/` and `NN/Cost/Enclose.lean`, the size fact
`NeurNetContrSysDT.reach_order_le`, and a caller-supplied bound `hEnc` on the
controller's own output; nothing in it is asserted.

`hEnc` is the one thing `LinearSysDT.reachCost_le` never needed: there, `U` was
a caller's fixed set with a known `.h`. Here `U` is recomputed every step by
`NeuralNetwork.enclose`, whose output size no `Complexity/` fact bounds in
general, so the bound is a hypothesis rather than a derivation.
-/
