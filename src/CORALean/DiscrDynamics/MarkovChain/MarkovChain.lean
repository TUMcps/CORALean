module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# A Markov chain over a grid partition: the representation

CORA's `markovchain` (`discrDynamics/@markovchain`): a `GridPartition` `field` and the
transition probabilities `T` between its cells, one pair of matrices per discrete input.
Row and column `0` of each matrix are the outside, and a column `s` holds the probabilities
`P(cell r | cell s)`, so a built column sums to one. `T.T` is the transition after the sampling
time, `T.OT` the one averaged over it.

Before `convertTransitionMatrix` the matrices are a cell array over the inputs (`Transitions`);
after it and in `stretch` one matrix over the pairs of cell and input (`Stacked`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `T` of a chain with `m` inputs and `N` cells: `T.T` and `T.OT` per input. -/
structure MarkovChain.Transitions (m N : ℕ) where
  T : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  OT : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ

/-- A Markov chain over a grid partition `field`, with `m` discrete inputs. -/
structure MarkovChain (n m : ℕ) where
  field : GridPartition n
  T : MarkovChain.Transitions m field.nrOfCells

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
