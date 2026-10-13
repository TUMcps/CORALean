import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# A value below every level that fails is below the telescoped layers

The pointwise step behind `pyramid`: take increasing levels `L 0 ≤ ... ≤ L k`, and a point
that is in layer `i` for some of the `i < k`. If the value `v` at the point is at most `L i`
for every layer `i` it is not in, and at most `L k`, then `v ≤ L 0 + Σ_{i in} (L (i+1) - L i)`.
The layers it is in need not form an initial segment. Induction on `k`, peeling layer `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Finset


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_add_sum_levels : ∀ {k : ℕ} (L : Fin (k + 1) → ℝ) (p : Fin k → Prop)
    [DecidablePred p] (v : ℝ), (∀ i : Fin k, L i.castSucc ≤ L i.succ) →
    (∀ i, ¬ p i → v ≤ L i.castSucc) → v ≤ L (Fin.last k) →
    v ≤ L 0 + ∑ i, if p i then L i.succ - L i.castSucc else 0 := by -- --- PROOF ---
  intro k
  -- induction on the number of layers
  induction k with
  | zero =>
    intro L p _ v _ _ hlast
    simpa using hlast
  | succ k ih =>
    intro L p _ v hmono hnot hlast
    -- the sum of non-negative steps is non-negative
    have hnn : 0 ≤ ∑ i : Fin (k + 1), if p i then L i.succ - L i.castSucc else 0 :=
      Finset.sum_nonneg fun i _ => by
        split_ifs
        · linarith [hmono i]
        · exact le_rfl
    -- peel layer `0`: in it, the claim for the shifted levels; out of it, `v ≤ L 0`
    by_cases h0 : p 0
    · have key := ih (fun i => L i.succ) (fun i => p i.succ) v (fun i => hmono i.succ)
        (fun i hi => hnot i.succ hi) hlast
      rw [Fin.sum_univ_succ]
      simp only [h0, if_true, Fin.succ_zero_eq_one, Fin.castSucc_zero]
      simp only [Fin.succ_zero_eq_one, Fin.succ_castSucc] at key
      linarith
    · have := hnot 0 h0
      simp only [Fin.castSucc_zero] at this
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
