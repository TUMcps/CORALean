import Mathlib.Data.List.Range
import Mathlib.Logic.Function.Iterate

/-!
# A loop that steps a state and records its outputs

`k` passes of a loop that replaces the state by `step` and appends `out` of the new state to a
list, started at `(s₀, [out s₀])`, end at `step^[k] s₀` with the outputs `out (step^[j] s₀)`
for `j ≤ k`. The reach algorithms of `LinearSys` run this loop over their time windows.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` passes of a loop that steps its state and appends what the new state outputs. -/
theorem foldl_range_step_out {σ β : Type} (step : σ → σ) (out : σ → β) (s₀ : σ) (k : ℕ) :
    (List.range k).foldl (fun (P : σ × List β) (_ : ℕ) => (step P.1, P.2 ++ [out (step P.1)]))
      (s₀, [out s₀])
      = (step^[k] s₀,
        (List.range (k + 1)).map fun j => out (step^[j] s₀)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.range_succ, Function.iterate_succ_apply']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
