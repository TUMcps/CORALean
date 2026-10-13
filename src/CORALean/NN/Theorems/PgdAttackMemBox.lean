import CORALean.NN.Operations.PgdAttack

/-!
# The PGD attack stays in the box and within `ε` of its input

CORA's guarantees for `computePGDAttack`: the result lies in `[l, u]` and within `ε` of `x` in the
sup norm. Both come from the last clip: `z ∈ [max(l, x - ε), min(u, x + ε)]`, which is nonempty
exactly when the hypothesis holds, and at least one pass has run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.pgdAttack_mem_box (c : Chain n m) (x : Vec ℝ n) (t : Vec ℝ m) (ε : ℝ) {Q : ℕ}
    (hQ : 0 < Q) (l u : Vec ℝ n) (stepsize stepsizeDecay : ℝ) (stepsizeDecayIter : List ℕ)
    (lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m) (z : Vec ℝ n)
    (hz : z = c.pgdAttack x t ε Q l u stepsize stepsizeDecay stepsizeDecayIter lossDer)
    (hbox : ∀ i, max (l i) (x i - ε) ≤ min (u i) (x i + ε)) (i : Fin n) :
    l i ≤ z i ∧ z i ≤ u i ∧ |z i - x i| ≤ ε := by -- --- PROOF ---
  subst hz
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hQ.ne'
  have h := hbox i
  have key : ∀ w : ℝ,
      l i ≤ min (min (u i) (x i + ε)) (max (max (l i) (x i - ε)) w) ∧
      min (min (u i) (x i + ε)) (max (max (l i) (x i - ε)) w) ≤ u i ∧
      |min (min (u i) (x i + ε)) (max (max (l i) (x i - ε)) w) - x i| ≤ ε := by
    intro w
    have hlo : x i - ε ≤ min (min (u i) (x i + ε)) (max (max (l i) (x i - ε)) w) :=
      le_min (le_trans (le_max_right _ _) h) (le_max_of_le_left (le_max_right _ _))
    have hhi : min (min (u i) (x i + ε)) (max (max (l i) (x i - ε)) w) ≤ x i + ε :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    exact ⟨le_min (le_trans (le_max_left _ _) h) (le_max_of_le_left (le_max_left _ _)),
      le_trans (min_le_left _ _) (min_le_left _ _), abs_le.mpr ⟨by linarith, by linarith⟩⟩
  simp only [Chain.pgdAttack, Chain.pgdStep]
  exact key _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
