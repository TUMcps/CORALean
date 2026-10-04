import CORALean.ContDynamics.NonlinearSys.Operations.Identify
import CORALean.Global.DmdSelectLe

/-!
# `identify` is no worse than the full-rank candidate

`identify` returns the system of one of the candidates of ranks `1, …, rankMax`, and its `err` is
at most that of every one of them, the full-rank candidate among them, for a comparison `lt`
that is `<`. Only as good as `err`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m N r d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.identify_le_candidate (φ : Vec ℝ n → Vec ℝ m → Vec ℝ d) (lt : ℝ → ℝ → Bool)
    (hlt : ∀ a b, lt a b = true ↔ a < b) (err : NonlinearSys n m → ℝ) (dx : Fin N → Vec ℝ n)
    (V : Mat ℝ d r) (s : Fin r → ℝ) (W : Mat ℝ N r) (hr : 0 < r) :
    ∃ sys, NonlinearSys.identify φ lt err dx V s W = some sys ∧
      (∃ k, 1 ≤ k ∧ k ≤ r ∧ sys = (NonlinearSys.mk fun x u =>
        NonlinearSys.identifyCandidate dx V s W k *ᵥ φ x u)) ∧
      err sys ≤ err (NonlinearSys.mk fun x u =>
        NonlinearSys.identifyCandidate dx V s W r *ᵥ φ x u) := by
  obtain ⟨M, hM, hk, hle⟩ := dmdSelect_le lt hlt err
    (fun k => (NonlinearSys.mk fun x u =>
      NonlinearSys.identifyCandidate dx V s W k *ᵥ φ x u)) hr
  exact ⟨M, hM, hk, hle r hr le_rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
