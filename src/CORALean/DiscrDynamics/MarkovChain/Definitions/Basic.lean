module

public import CORALean.DiscrDynamics.MarkovChain.MarkovChain
public import Mathlib.LinearAlgebra.Matrix.Stochastic

@[expose] public section

/-!
# `DiscrDynamics/MarkovChain/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n m : ℕ}


-- ================================  `MarkovChain.FinalStates`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `finalStateMat`: the final states of the simulated runs, at the time point and over time. -/
structure MarkovChain.FinalStates (n : ℕ) where
  T : List (Vec ℝ n)
  OT : List (Vec ℝ n)


-- ================================  `MarkovChain.IsStochastic`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every transition matrix is column-stochastic: each column is a distribution. -/
def MarkovChain.IsStochastic (M : MarkovChain n m) : Prop :=
  ∀ i, M.T.T i ∈ Matrix.colStochastic ℝ (Fin (M.field.nrOfCells + 1)) ∧
    M.T.OT i ∈ Matrix.colStochastic ℝ (Fin (M.field.nrOfCells + 1))


-- =================================  `MarkovChain.ReachEntry`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One `R(k)` of a `reachSet` array: its last time-point set and its time-interval sets. -/
structure MarkovChain.ReachEntry (S : ℕ → Type) (n : ℕ) where
  timePoint : S n
  timeInterval : List (S n)


-- ==================================  `MarkovChain.Stacked`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `T` after `convertTransitionMatrix`: one matrix per field over the states. -/
structure MarkovChain.Stacked (ι : Type) where
  T : Matrix ι ι ℝ
  OT : Matrix ι ι ℝ


-- =================================  `MarkovChain.Converted`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `[T, projMat, GammaFull]`, over the pairs (cell, input) of `N` cells and `m` inputs. -/
structure MarkovChain.Converted (N m : ℕ) where
  T : MarkovChain.Stacked (Fin (N + 1) × Fin m)
  projMat : Matrix (Fin (N + 1)) (Fin (N + 1) × Fin m) ℝ
  GammaFull : Matrix (Fin (N + 1) × Fin m) (Fin (N + 1) × Fin m) ℝ


-- ==========================  `MarkovChain.TransitionProbabilities`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `tp`: the probabilities of reaching the outside and each cell, `T` and `OT`. -/
structure MarkovChain.TransitionProbabilities (N : ℕ) where
  T : Fin (N + 1) → ℝ
  OT : Fin (N + 1) → ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
