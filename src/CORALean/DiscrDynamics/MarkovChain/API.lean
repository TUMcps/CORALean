module

public import CORALean.DiscrDynamics.MarkovChain.MarkovChain
public import CORALean.DiscrDynamics.MarkovChain.Definitions.API
public import CORALean.DiscrDynamics.MarkovChain.Operations.API
public import CORALean.DiscrDynamics.MarkovChain.Theorems.API
public import CORALean.DiscrDynamics.MarkovChain.Counterexamples.API

/-!
# The Markov chain over a partition

CORA's `markovchain` (`discrDynamics/@markovchain`): the transition probabilities between the
cells of a `GridPartition`, one pair of matrices per discrete input. `Operations/` holds CORA's
methods, `Theorems/` what they guarantee: a built column is a distribution, `build_reach` moves
only into cells the reachable sets meet, the conversion and `stretch` keep columns stochastic.
`Counterexamples/` holds the reachable set of volume zero that breaks CORA's `build_reach`.
-/
