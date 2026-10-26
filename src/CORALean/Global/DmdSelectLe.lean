module

public import CORALean.Global.DmdSelect

@[expose] public section

/-!
# The selected candidate has the least error

`dmdSelect` returns one of the candidates of ranks `1, …, rankMax` and none of them has a
smaller error, in particular not the full-rank one. Only as good as `err`: nothing here says
a small `err` is a fit.
The source is [1].

## Inputs
* `lt` – strict comparison of errors
* `err` – error of a candidate
* `cand` – candidate for each rank
* `rankMax` – largest rank

## Hypotheses
* `hlt` – the comparison is the strict order on errors
* `hr` – some rank is tried

## Conclusion
* the selected candidate is one of the candidates and no candidate has a smaller error

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the loop holds after `rankMax` ranks: a pair or nothing, nothing only for none. -/
private theorem aux_dmdSelect_fold (lt : ℝ → ℝ → Bool) (hlt : ∀ a b, lt a b = true ↔ a < b)
    (err : α → ℝ) (cand : ℕ → α) (rankMax : ℕ) : -- --- CONCL ---
    ((List.range rankMax).foldl (fun best i =>
      match best with
      | none => some (cand (i + 1), err (cand (i + 1)))
      | some (_, errBest) =>
        if lt (err (cand (i + 1))) errBest then some (cand (i + 1), err (cand (i + 1))) else best)
      none = none ∧ rankMax = 0) ∨
    ∃ M e, ((List.range rankMax).foldl (fun best i =>
      match best with
      | none => some (cand (i + 1), err (cand (i + 1)))
      | some (_, errBest) =>
        if lt (err (cand (i + 1))) errBest then some (cand (i + 1), err (cand (i + 1))) else best)
      none = some (M, e)) ∧ e = err M ∧ (∃ k, 1 ≤ k ∧ k ≤ rankMax ∧ M = cand k) ∧
      ∀ k, 1 ≤ k → k ≤ rankMax → e ≤ err (cand k) := by -- --- PROOF ---
  induction rankMax with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases ih with ⟨h, hr⟩ | ⟨M, e, hf, he, ⟨k0, hk0, hk0r, hM⟩, hle⟩
    · -- the first rank is taken whatever its error
      subst hr
      rw [h]
      refine Or.inr ⟨cand (0 + 1), err (cand (0 + 1)), rfl, rfl, ⟨1, le_rfl, le_rfl, rfl⟩, ?_⟩
      intro k hk1 hk2
      obtain rfl : k = 1 := by omega
      exact le_rfl
    · rw [hf]
      simp only
      by_cases hl : lt (err (cand (r + 1))) e = true
      · -- a strictly smaller error replaces the best so far
        rw [if_pos hl]
        refine Or.inr ⟨_, _, rfl, rfl, ⟨r + 1, by omega, le_rfl, rfl⟩, fun k hk1 hk2 => ?_⟩
        rcases Nat.lt_or_ge k (r + 1) with hk | hk
        · exact le_trans ((hlt _ _).mp hl).le (he ▸ hle k hk1 (by omega))
        · obtain rfl : k = r + 1 := by omega
          exact le_rfl
      · -- otherwise the best stays
        rw [if_neg hl]
        have hge : e ≤ err (cand (r + 1)) := not_lt.mp (fun h => hl ((hlt _ _).mpr h))
        refine Or.inr ⟨M, e, rfl, he, ⟨k0, hk0, by omega, hM⟩, fun k hk1 hk2 => ?_⟩
        rcases Nat.lt_or_ge k (r + 1) with hk | hk
        · exact hle k hk1 (by omega)
        · obtain rfl : k = r + 1 := by omega
          exact hge


-- =======================================  MAIN THEOREM  ======================================= --

theorem dmdSelect_le (lt : ℝ → ℝ → Bool) (hlt : ∀ a b, lt a b = true ↔ a < b)
    (err : α → ℝ) (cand : ℕ → α) {rankMax : ℕ} (hr : 0 < rankMax) :
    ∃ M, dmdSelect lt err cand rankMax = some M ∧ (∃ k, 1 ≤ k ∧ k ≤ rankMax ∧ M = cand k) ∧
      ∀ k, 1 ≤ k → k ≤ rankMax → err M ≤ err (cand k) := by
  unfold dmdSelect
  rcases aux_dmdSelect_fold lt hlt err cand rankMax with ⟨_, h0⟩ | ⟨M, e, hf, he, hk, hle⟩
  · omega
  · exact ⟨M, congrArg (Option.map Prod.fst) hf, hk, fun k hk1 hk2 => he ▸ hle k hk1 hk2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
