module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.Identify
public import CORALean.Global.DmdSelectLe

@[expose] public section

/-!
# `identify` is no worse than the full-rank candidate

`identify` returns the system of one of the candidates of ranks `1, …, rankMax`, and its `err` is
at most that of every one of them, the full-rank candidate among them, for a comparison `lt`
that is `<`. Only as good as `err`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m N r d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.identify_le_candidate (φ : Vec ℝ n → Vec ℝ m → Vec ℝ d) (dt : ℝ)
    (lt : ℝ → ℝ → Bool)
    (hlt : ∀ a b, lt a b = true ↔ a < b) (err : NonlinearSysDT n m → ℝ) (xNext : Fin N → Vec ℝ n)
    (V : Mat ℝ d r) (s : Fin r → ℝ) (W : Mat ℝ N r) (hr : 0 < r) :
    ∃ sys, NonlinearSysDT.identify φ dt lt err xNext V s W = some sys ∧
      (∃ k, 1 ≤ k ∧ k ≤ r ∧ sys = (NonlinearSysDT.mk (fun x u =>
        NonlinearSysDT.identifyCandidate xNext V s W k *ᵥ φ x u) n
        (fun x _ => x) dt)) ∧
      err sys ≤ err (NonlinearSysDT.mk (fun x u =>
        NonlinearSysDT.identifyCandidate xNext V s W r *ᵥ φ x u) n
        (fun x _ => x) dt) := by -- --- PROOF ---
  obtain ⟨M, hM, hk, hle⟩ := dmdSelect_le lt hlt err
    (fun k => (NonlinearSysDT.mk (fun x u =>
      NonlinearSysDT.identifyCandidate xNext V s W k *ᵥ φ x u) n
      (fun x _ => x) dt)) hr
  exact ⟨M, hM, hk, hle r hr le_rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
