module

public import CORALean.DiscrDynamics.MarkovChain.Operations.ReachProbability
public import CORALean.DiscrDynamics.MarkovChain.Theorems.SumZipWithEqZero
public import CORALean.DiscrDynamics.GridPartition.Theorems.ExactIntersectingCellsSupport

@[expose] public section

/-!
# `reachProbability` is supported on the intersecting cells

The soundness of `build_reach`: a cell with nonzero transition probability is one the
over-approximation `intersectingCellsOf` returns for some reachable set, so the chain moves
only into cells the reachable sets meet.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A cell `s ≠ 0` with `tp.T s ≠ 0` meets the hull of the time-point set of some `R(k)`. -/
theorem MarkovChain.reachProbability_T_support (field : GridPartition n) (hn : n ≠ 0)
    (R : List (MarkovChain.ReachEntry S n)) (tranFrac : List ℝ)
    {s : Fin (field.nrOfCells + 1)} (hs : s ≠ 0)
    (h : (MarkovChain.reachProbability field R tranFrac).T s ≠ 0) : -- --- CONCL ---
    ∃ r ∈ R, (s : ℕ) ∈ field.intersectingCellsOf r.timePoint := by -- --- PROOF ---
  have hs1 : 1 ≤ (s : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h0 => hs (Fin.ext h0))
  have hs2 : (s : ℕ) ≤ field.nrOfCells := Nat.lt_succ_iff.mp s.isLt
  by_contra hcon
  push Not at hcon
  apply h
  unfold MarkovChain.reachProbability
  dsimp only
  -- every term vanishes: its `iProp` entry would put the cell in the hull's list
  apply MarkovChain.sum_zipWith_eq_zero
  intro r hr f
  have : (field.exactIntersectingCells r.timePoint).iProp.getD s 0 = 0 := by
    by_contra hne
    exact hcon r hr (field.exactIntersectingCells_support _ hn hs1 hs2 hne)
  rw [this, mul_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
