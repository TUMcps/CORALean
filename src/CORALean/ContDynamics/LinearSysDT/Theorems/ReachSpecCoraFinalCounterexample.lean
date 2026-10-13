module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachSpecCora
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's `linearSysDT/reach` never checks the specification at `tFinal`

`x⁺ = x + 1` from `R0 = {0}` with `dt = tFinal = 1` is one step. The loop checks `Rout{1} = {0}`
only; `Rout{2} = {1}` is computed after it. Against the unsafe set `[1/2, 3/2]` the state
`x(1) = 1` is unsafe, yet `res = true`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `res = true`, although the state reached at `tFinal` is in the unsafe set. -/
theorem LinearSysDT.reachSpecCora_final_counterexample :
    LinearSysDT.reachSpecCora 1 1 {0} (Set.Icc (1 / 2) (3 / 2)) 1 ∧
      ∃ x₀ ∈ ({0} : Set ℝ), 1 * x₀ + 1 ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by -- --- PROOF ---
  refine ⟨?_, 0, rfl, by constructor <;> norm_num⟩
  intro i hi
  have : i = 1 := by simpa using hi
  subst this
  simp only [Nat.sub_self, Function.iterate_zero]
  rw [Set.disjoint_left]
  rintro x ⟨y, hy, rfl⟩ ⟨h, -⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  norm_num at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
