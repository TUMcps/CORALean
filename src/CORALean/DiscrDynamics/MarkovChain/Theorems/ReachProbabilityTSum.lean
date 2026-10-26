module

public import CORALean.DiscrDynamics.MarkovChain.Operations.ReachProbability
public import CORALean.DiscrDynamics.GridPartition.Theorems.ExactIntersectingCellsSum

@[expose] public section

/-!
# `reachProbability` conserves the weights

Each `iProp` sums to one, so the transition probabilities add up to the sum of the weights
`tranFrac{k}`: one, for weights that are probabilities, as `priv_transitionFraction` gives.

## Inputs
* `field` – grid partition
* `R` – reach sets
* `tranFrac` – weights of the reach sets

## Hypotheses
* none

## Conclusion
* the probabilities sum to the sum of the weights
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Summing a weighted `zipWith` over the index summing each term. -/
private theorem MarkovChain.aux_sum_comm_zipWith {α ι : Type} [Fintype ι] (a : α → ι → ℝ)
    (R : List α) (F : List ℝ) : -- --- CONCL ---
    ∑ s, (List.zipWith (fun r f => f * a r s) R F).sum =
      (List.zipWith (fun r f => f * ∑ s, a r s) R F).sum := by -- --- PROOF ---
  induction R generalizing F with
  | nil => simp
  | cons x R ih =>
    cases F with
    | nil => simp
    | cons f F =>
      simp only [List.zipWith_cons_cons, List.sum_cons, Finset.sum_add_distrib, ih, Finset.mul_sum]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entries of `tp.T` sum to the sum of the weights used. -/
theorem MarkovChain.reachProbability_T_sum (field : GridPartition n)
    (R : List (MarkovChain.ReachEntry S n)) (tranFrac : List ℝ) : -- --- CONCL ---
    ∑ s, (MarkovChain.reachProbability field R tranFrac).T s = (tranFrac.take R.length).sum
      := by -- --- PROOF ---
  unfold MarkovChain.reachProbability
  dsimp only
  rw [MarkovChain.aux_sum_comm_zipWith (ι := Fin (field.nrOfCells + 1))
    (fun r s => (field.exactIntersectingCells r.timePoint).iProp.getD (s : ℕ) 0) R tranFrac]
  simp only [field.exactIntersectingCells_sum, mul_one]
  induction R generalizing tranFrac with
  | nil => simp
  | cons x R ih =>
    cases tranFrac with
    | nil => simp
    | cons f F => simp [ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
