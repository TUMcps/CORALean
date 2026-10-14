module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `LinearSys.fromStartTimePointCora`: the constant input of `fromStart` with `U = {0}`

`priv_reach_fromStart.m` propagates the time-point set of step `k` as `Htp = Q * Htp_0` and adds
the particular solution `PU` of the earlier steps. The accumulation
`PU = reduce(PU + Q * PU_0 + P * Pu_0, ...)` (l. 93-96) stands inside `if isa(PU,'contSet')`. For
`U = {0}` (`canonicalForm` gives `U_ = B*U + E*W = {0}`) the first step's `PU_0` is the numeric
`zeros(n,1)` (`particularSolution_timeVarying` returns `block_zeros(blocks)` for an origin, l.
48-50), so the test fails at every step and the constant input `Pu_0` of the steps `2, ..., k - 1`
is never added. `priv_reach_decomp.m` accumulates before its test and is not affected.

Modelled for `R0 = {0}`, `U = {0}` in `ℝ`, where every set is a point: `e` is `e^{AΔt}` (`eAdt`) and
`pu0` the constant-input solution of the first step (`Pu_0`), which is also `Htp_0` for `R0 = {0}`.
Read from the source, not run.

# CORA's `fromStart` loses the accumulated constant input

For `linearSys(0,0,1)` (`ẋ = 1`), `R0 = {0}`, `U = {0}`, `timeStep = 1`, `tFinal = 3`, `linAlg =
'fromStart'`: `e = 1`, `Pu_0 = 1`, and the time-point sets of CORA are `{1}, {1}, {1}`, where the
state is `1, 2, 3` at the three time points.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- The time-point set (a point) after step `k + 1` of `fromStart`: `Htp = Q * Htp_0` with
`Q = e ^ k`, plus `PU`, which stays the numeric `0` because `isa(PU,'contSet')` is false. -/
def LinearSys.fromStartTimePointCora (e htp0 : ℝ) (k : Nat) : ℝ :=
  e ^ k * htp0 + 0

/-- The state at the time point after `k` steps under the constant input, from the variation of
constants: `x_{k+1} = e * x_k + Pu_0`, `x_0 = 0`. -/
def LinearSys.constantInputTimePoint (e pu0 : ℝ) : Nat → ℝ
  | 0 => 0
  | k + 1 => e * LinearSys.constantInputTimePoint e pu0 k + pu0


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `e = 1` and `Pu_0 = 1` (`ẋ = 1`, `Δt = 1`) the set after step `k + 1` is `{1}`, and the
state is `k + 1`: from the second step on the state is outside CORA's set. -/
theorem LinearSys.fromStartTimePointCora_counterexample (k : Nat) :
    LinearSys.fromStartTimePointCora 1 1 k = 1 ∧
      LinearSys.constantInputTimePoint 1 1 (k + 1) = (k : ℝ) + 1 ∧
      (1 ≤ k → LinearSys.constantInputTimePoint 1 1 (k + 1) ∉
        ({LinearSys.fromStartTimePointCora 1 1 k} : Set ℝ)) := by -- --- PROOF ---
  have h : ∀ j : Nat, LinearSys.constantInputTimePoint 1 1 j = j := by
    intro j
    induction j with
    | zero => simp [LinearSys.constantInputTimePoint]
    | succ j ih => simp [LinearSys.constantInputTimePoint, ih]
  have h1 : LinearSys.fromStartTimePointCora 1 1 k = 1 := by
    simp [LinearSys.fromStartTimePointCora]
  refine ⟨h1, by simp [h], fun hk => ?_⟩
  rw [h1, h]
  simp only [Set.mem_singleton_iff]
  intro hc
  have : (2 : ℝ) ≤ ((k + 1 : Nat) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
