import CORALean.NN.Graph.Theorems.BallSubsetSucc
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Set.Monotone

/-!
# The ball always stabilises, in at most `N` rounds

Every ball is a `Finset (Fin N)`, so the growing chain `ball A v 0 ⊆ ball A v 1 ⊆ …`
cannot strictly grow past `N` steps before it repeats — the bound letting a caller
stop a breadth-first search after `N` rounds, not merely know it terminates
eventually. This computes nothing: `ball` still filters `Finset.univ` at every
radius, and finding the stable ball is left to a search, not stated here.

Were no `r ≤ N` stable, the cardinalities would be strictly increasing on
`[0, N + 1]`, forcing `N + 1 ≤ (ball A v (N + 1)).card ≤ N` by `Finset.card_le_univ` —
absurd. The strictly-increasing-implies-`id`-bounded step is Mathlib's monotone
chain machinery, `strictMonoOn_Iic_of_lt_succ`/`StrictMonoOn.Iic_id_le`, not
hand-rolled.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The ball stops growing at some radius no larger than `N`, so a caller never
needs more than `N` rounds to find its fixpoint. -/
theorem GNN.exists_ball_stable {N : ℕ} (A : Mat ℝ N N) (v : Fin N) :
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
