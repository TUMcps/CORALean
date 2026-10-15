module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic
public import CORALean.DiscrDynamics.GridPartition.Operations.ExactIntersectingCells

@[expose] public section

/-!
# `MarkovChain.reachProbability`

`priv_transitionProbability_reach`: for each `R(k)`, the volume shares `exactIntersectingCells`
gives its last time-point set, weighted by `tranFrac{k}`, add up to `tp.T`; those of each of its
time-interval sets, weighted by `tranFrac{k}` over their number, to `tp.OT`.

CORA adds a one-entry `iProp = 1` (a set of volume zero) to every entry; here it is `1` padded
with zeros, that is, the entry for the outside. See `reachProbabilityCora`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `tp = priv_transitionProbability_reach(R, tranFrac, field)`: volume shares, weighted. -/
noncomputable def MarkovChain.reachProbability {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [Real.IntervalOuter S] (field : GridPartition n) (R : List (MarkovChain.ReachEntry S n))
    (tranFrac : List ℝ) : MarkovChain.TransitionProbabilities field.nrOfCells where
  T := fun s => (List.zipWith (fun r f =>
    f * (field.exactIntersectingCells r.timePoint).iProp.getD s 0) R tranFrac).sum
  OT := fun s => (List.zipWith (fun r f => (r.timeInterval.map fun X =>
    f / r.timeInterval.length * (field.exactIntersectingCells X).iProp.getD s 0).sum) R
    tranFrac).sum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
