module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachSpecCora
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's `nonlinearSysDT/reach` never checks the initial set against the specification

`x⁺ = x + 1` from `R0 = {0}` for one step, against the unsafe set `[-1/2, 1/2]`: the initial
state `0` is unsafe, yet `res = true` (the later sets `{1}` are safe). No other code checks
`R0` first: `reach` is the entry point and `check` is called only at l. 87.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `res = true`, although the initial state `0` is in the unsafe set. -/
theorem NonlinearSysDT.reachSpecCora_initial_counterexample :
    NonlinearSysDT.reachSpecCora (fun i => (fun x : ℝ => x + 1)^[i] '' {0})
        (Set.Icc (-1 / 2) (1 / 2)) 1 ∧
      (0 : ℝ) ∈ ({0} : Set ℝ) ∩ Set.Icc (-1 / 2) (1 / 2) := by -- --- PROOF ---
  refine ⟨?_, rfl, by constructor <;> norm_num⟩
  intro i hi
  have : i = 1 := by simpa using hi
  subst this
  simp only [Nat.add_sub_cancel, Function.iterate_one, Set.image_singleton, zero_add]
  rw [Set.disjoint_singleton_left]
  rintro ⟨-, h⟩
  norm_num at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
