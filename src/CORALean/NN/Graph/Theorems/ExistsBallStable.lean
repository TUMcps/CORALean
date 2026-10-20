module

public import CORALean.NN.Graph.Theorems.BallSubsetSucc
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.Monotone

@[expose] public section

/-!
# The ball always stabilises, in at most `N` rounds

Every ball is a `Finset (Fin N)`, so the growing chain `ball A v 0 ⊆ ball A v 1 ⊆ …` cannot strictly
grow past `N` steps before it repeats — the bound letting a caller stop a breadth-first search after
`N` rounds. This computes nothing: `ball` still filters `Finset.univ` at every radius.

Were no `r ≤ N` stable, the cardinalities would be strictly increasing on `[0, N + 1]`, forcing `N +
1 ≤ (ball A v (N + 1)).card ≤ N` by `Finset.card_le_univ`, which is absurd. The step is Mathlib's
`strictMonoOn_Iic_of_lt_succ`/`StrictMonoOn.Iic_id_le`.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node

## Hypotheses
* none

## Conclusion
* the ball stops growing at some radius at most N
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The ball stops growing at some radius no larger than `N`, so a caller never
needs more than `N` rounds to find its fixpoint. -/
theorem GNN.exists_ball_stable {N : ℕ} (A : Mat ℝ N N) (v : Fin N) : -- --- CONCL ---
    ∃ r ≤ N, GNN.ball A v (r + 1) = GNN.ball A v r := by -- --- PROOF ---
  by_contra hcon
  push Not at hcon
  have hlt : ∀ m, m < N + 1 → (GNN.ball A v m).card < (GNN.ball A v (m + 1)).card := by
    intro m hm
    exact Finset.card_lt_card
      ((GNN.ball_subset_succ A v m).ssubset_of_ne (hcon m (Nat.lt_succ_iff.mp hm)).symm)
  have hmono : StrictMonoOn (fun r => (GNN.ball A v r).card) (Set.Iic (N + 1)) :=
    strictMonoOn_Iic_of_lt_succ hlt
  have hbound : N + 1 ≤ (GNN.ball A v (N + 1)).card := hmono.Iic_id_le (N + 1) le_rfl
  have hcard : (GNN.ball A v (N + 1)).card ≤ N := by
    calc (GNN.ball A v (N + 1)).card ≤ Fintype.card (Fin N) := Finset.card_le_univ _
      _ = N := Fintype.card_fin N
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
