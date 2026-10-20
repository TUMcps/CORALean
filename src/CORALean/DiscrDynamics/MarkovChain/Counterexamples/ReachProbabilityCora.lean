module

public import CORALean.DiscrDynamics.MarkovChain.Operations.ReachProbability
public import CORALean.DiscrDynamics.GridPartition.Theorems.ExactIntersectingCellsOfVolumeLe

@[expose] public section

/-!
# `MarkovChain.reachProbabilityCora`: CORA's `priv_transitionProbability_reach` as printed

`tp.T = tp.T + tranFrac{k}*iP_tp` with `tp.T` the `(nrOfStates + 1) × 1` zero column and
`iP_tp` the second output of `exactIntersectingCells`. The model adds `iP_tp` to `tp.T` the way
MATLAB does when `iP_tp` has a single entry: to every entry.

# A reachable set of volume zero breaks `build_reach`

`exactIntersectingCells` returns `iS = 0` and `iProp = 1`, a single entry, when `volume(P) ≤ 0`
(`if volTotal > 0` is false, so `iProp` stays empty and `proportionOutside = 1`). In
`priv_transitionProbability_reach` that scalar is added to the column `tp.T` of `nrOfStates + 1`
entries by implicit expansion, so every entry becomes `tranFrac{k}` and the column adds up to
`(nrOfStates + 1) tranFrac{k}`, not `tranFrac{k}`: a set of zero volume, such as a lower-dimensional
zonotope, would have the whole outside as its probability. `reachProbability` pads the
single entry with zeros instead, which puts the weight on the outside.

## Inputs
* `field` – grid partition
* `X` – set

## Hypotheses
* `hN` – partition has cells
* `h` – set has no positive volume

## Conclusion
* CORA's probabilities are one per state and do not sum to one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `tp.T` as printed: an `iProp` of one entry is added to every entry of the column. -/
noncomputable def MarkovChain.reachProbabilityCora (field : GridPartition n)
    (R : List (MarkovChain.ReachEntry S n)) (tranFrac : List ℝ) : Fin (field.nrOfCells + 1) → ℝ :=
  fun s => (List.zipWith (fun r f =>
    -- MATLAB's implicit expansion of a 1×1 array over the column
    let iP := (field.exactIntersectingCells r.timePoint).iProp
    f * iP.getD (if iP.length = 1 then 0 else s) 0) R tranFrac).sum


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a reachable set of volume zero, every entry of CORA's `tp.T` is the weight, so a column of
`nrOfStates + 1 > 1` entries does not add up to it. -/
theorem MarkovChain.reachProbabilityCora_counterexample (field : GridPartition n) (X : S n)
    (hN : 0 < field.nrOfCells) (h : ¬ 0 < GridPartition.volumeOf (construct X)) :
    (∀ s, MarkovChain.reachProbabilityCora field [⟨X, []⟩] [(1 : ℝ)] s = 1) ∧
      ∑ s, MarkovChain.reachProbabilityCora field [⟨X, []⟩] [(1 : ℝ)] s ≠ 1 := by -- --- PROOF ---
  have hs : ∀ s, MarkovChain.reachProbabilityCora field [⟨X, []⟩] [(1 : ℝ)] s = 1 := by
    intro s
    simp [MarkovChain.reachProbabilityCora,
      GridPartition.exactIntersectingCells_of_volume_le field X h]
  refine ⟨hs, ?_⟩
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (1 : ℝ) < (field.nrOfCells + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ hN
  exact ne_of_gt this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
