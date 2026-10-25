module

public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# `LinearSysDT.IsReachSpecCora`

The verdict `res` of CORA's `@linearSysDT/reach.m` called with an unsafe-set specification, for
`ℝ¹`, `B = 0`, no disturbance, no noise, `C = 1`, `D = 0` (so `outputSet` returns its argument,
ll. 91, 152) and `linAlg = 'standard'`. `Rnext.tp` starts at `R0` (l. 82) and is mapped by
`x ↦ A x + c` in the step of l. 99. The loop `for i = 1:steps` (l. 85) stores the output set at
the beginning of step `i`, `Rout{i} = Rnext.tp` after `i - 1` steps (l. 91), and checks that one
against the specification (l. 129). After the loop `Rout{end} = Rout{steps+1}` is computed
(l. 152) and returned, never checked.

# CORA's `linearSysDT/reach` never checks the specification at `tFinal`

`x⁺ = x + 1` from `R0 = {0}` with `dt = tFinal = 1` is one step. The loop checks `Rout{1} = {0}`
only; `Rout{2} = {1}` is computed after it. Against the unsafe set `[1/2, 3/2]` the state
`x(1) = 1` is unsafe, yet `res = true`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's verdict is true although the final state is unsafe
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `res`: every checked output set is disjoint from the unsafe set. -/
def LinearSysDT.IsReachSpecCora (A c : ℝ) (R₀ F : Set ℝ) (steps : ℕ) : Prop :=
  let Rtp : ℕ → Set ℝ := fun k => (fun x => A * x + c)^[k] '' R₀    -- 82, 99. Rnext.tp
  let Rout : ℕ → Set ℝ := fun i => Rtp (i - 1)                      -- 91. Rout{i}
  ∀ i ∈ Finset.Icc 1 steps, Disjoint (Rout i) F                -- 85, 129. check(spec,Rout{i})


-- =======================================  MAIN THEOREM  ======================================= --

/-- `res = true`, although the state reached at `tFinal` is in the unsafe set. -/
theorem LinearSysDT.reachSpecCora_final_counterexample : -- --- CONCL ---
    LinearSysDT.IsReachSpecCora 1 1 {0} (Set.Icc (1 / 2) (3 / 2)) 1 ∧
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
