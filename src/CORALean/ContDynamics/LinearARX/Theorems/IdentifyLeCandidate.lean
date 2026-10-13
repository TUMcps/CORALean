import CORALean.ContDynamics.LinearARX.Operations.Identify
import CORALean.Global.DmdSelectLe

/-!
# `identify` is no worse than the full-rank candidate

`identify` returns the blocks of one of the candidates of ranks `1, …, rankMax`, and its `err`
is at most that of every one of them, the full-rank candidate among them, for a comparison `lt`
that is `<`. Only as good as `err`. The source is [1].

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.identify_le_candidate (lt : ℝ → ℝ → Bool) (hlt : ∀ a b, lt a b = true ↔ a < b)
    (err : Mat ℝ dy (p * dy + (p + 1) * du) → ℝ) (yNext : Fin N → Vec ℝ dy)
    (V : Mat ℝ (p * dy + (p + 1) * du) r) (s : Fin r → ℝ) (W : Mat ℝ N r) (hr : 0 < r) :
    ∃ M, LinearARX.identify lt err yNext V s W = some (LinearARX.identifyBlocks M) ∧
      (∃ k, 1 ≤ k ∧ k ≤ r ∧ M = LinearARX.identifyCandidate yNext V s W k) ∧
      err M ≤ err (LinearARX.identifyCandidate yNext V s W r) := by -- --- PROOF ---
  obtain ⟨M, hM, hk, hle⟩ := dmdSelect_le lt hlt err (LinearARX.identifyCandidate yNext V s W) hr
  refine ⟨M, ?_, hk, hle r hr le_rfl⟩
  -- `identify` is the selection mapped through the blocks
  show Option.map LinearARX.identifyBlocks (dmdSelect lt err
    (LinearARX.identifyCandidate yNext V s W) r) = _
  rw [hM]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
