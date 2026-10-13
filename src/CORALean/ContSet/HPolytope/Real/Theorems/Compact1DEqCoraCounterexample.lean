import CORALean.ContSet.HPolytope.Real.Operations.Compact1DEqCora
import Mathlib.Tactic.FinCases

/-!
# CORA's `priv_compact_1D` moves a repeated equality constraint

The rows `2x = 1`, `2x = 1` describe `{½}`. `priv_compact_1D` normalizes both to `2x = 1` with
offset `1`, finds them equal and merges them into `Ae = 1; be = be(1) / Ae(1)`, which after the
first assignment is `1 / 1`: CORA returns `x = 1`, non-empty, and `½` is not in it
(`HPolytope.compact1DEqCora`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compact1DEqCora_counterexample :
    ∃ Q, HPolytope.compact1DEqCora ![2, 2] ![1, 1] = some (false, Q) ∧
      (fun _ => 1 / 2 : Vec ℝ 1) ∈ (HPolytope.ofEqs1D ![2, 2] ![1, 1]).construct ∧
      (fun _ => 1 / 2 : Vec ℝ 1) ∉ Q.construct := by -- --- PROOF ---
  refine ⟨HPolytope.ofEqs1D ![1] ![1], ?_, ?_, ?_⟩
  · simp [HPolytope.compact1DEqCora, Fin.exists_fin_two]
  · refine ⟨fun i => i.elim0, fun i => ?_⟩
    fin_cases i <;> simp [HPolytope.ofEqs1D]
  · intro h
    have := h.2 (show Fin 1 from 0)
    simp [HPolytope.ofEqs1D] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
