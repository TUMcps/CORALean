module

public import CORALean.ContDynamics.LinearSys.Operations.Identify
public import CORALean.Global.DmdSelectLe

@[expose] public section

/-!
# `identify` is no worse than the full-rank candidate

`identify` returns the blocks of one of the candidates of ranks `1, …, rankMax`, and
its `err` is at most that of every one of them, the full-rank candidate among them, for a
comparison `lt` that is `<`. Only as good as `err`.
The source is [1].

## References

* [1] `contDynamics/@linearSys/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.identify_le_candidate (lt : ℝ → ℝ → Bool)
    (hlt : ∀ a b, lt a b = true ↔ a < b)
    (err : Mat ℝ n (n + 1 + m) → ℝ) (dx : Fin N → Vec ℝ n)
    (V : Mat ℝ (n + 1 + m) r) (s : Fin r → ℝ) (W : Mat ℝ N r) (hr : 0 < r) : -- --- STMT ---
    ∃ M, LinearSys.identify lt err dx V s W =
        some (LinearSys.ofABc (dmdBlocks M).1 (dmdBlocks M).2.1 (dmdBlocks M).2.2) ∧
      (∃ k, 1 ≤ k ∧ k ≤ r ∧ M = LinearSys.identifyCandidate dx V s W k) ∧
      err M ≤ err (LinearSys.identifyCandidate dx V s W r) := by -- --- PROOF ---
  obtain ⟨M, hM, hk, hle⟩ := dmdSelect_le lt hlt err (LinearSys.identifyCandidate dx V s W) hr
  refine ⟨M, ?_, hk, hle r hr le_rfl⟩
  -- `identify` is the selection mapped through the blocks and `ofABc`
  show Option.map (fun M => LinearSys.ofABc (dmdBlocks M).1 (dmdBlocks M).2.1 (dmdBlocks M).2.2)
    (dmdSelect lt err (LinearSys.identifyCandidate dx V s W) r) = _
  rw [hM]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
