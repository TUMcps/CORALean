module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `LinParamSys.firstTimeIntervalCora`: the constant offset `c` is a time-varying input

The constructor of `linParamSys` takes a constant offset `c` (history: "10-September-2025 Add
constant input c"), and `priv_inputSolution.m` (l. 32) puts it into the input set
`V = B*params.U + c`. That set is treated as a time-varying input: `inputSet = V*r + ...` is added
to the hull of the whole step, `Rtotal = Rhom + Rinput` (`initReach.m` l. 50-58), which is a
solution of the time-interval question only when `0 ∈ V` (then `V*s ⊂ V*r` for `s <= r`). The
correction for a constant input, `inputCorr = inputF * zonotope(vTrans)` (`priv_inputSolution.m`),
covers `vTrans = B*uTrans` only, not `c`. `postProcessing.m` (`aux_set_originContained`) gives
`originContained = ~any(sys.c)` for `B = 0`, so for `c ≠ 0` the correction is computed, with
`vTrans = 0`. `post` (the branch without `uTransVec`) then adds `Rinput` to the previous interval
set, so the later steps inherit the error.
Modelled in `ℝ` for `ẋ = a x + c` with a certain `a` (an `intervalMatrix` of radius `0`),
`R0 = {0}`, `U = {0}`, `uTrans = 0`: `Rhom = enclose({0}, {0}) + F*{0} + 0 = {0}`, and `Rinput` is
the point `∫₀^r e^{as} c ds = c (e^{ar} - 1)/a` widened by `w`, the truncation error `E r Vabs` and
the reduction. Read from the source, not run.

# CORA's `linParamSys` time-interval set of the first step misses the start

For `A = intervalMatrix(-1, 0)` (`constParam`), `B = 0`, `c = 1`, `R0 = {0}`, `U = {0}`,
`timeStep = r`: the first time-interval set (`Rfirst.ti`) is the neighbourhood of `1 - e^{-r}`, the
state at the end of the step. The state at the start, `x(0) = 0`, is outside it (`w` is of the size
of the Taylor remainder, far below `1 - e^{-r}`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `Rfirst.ti = Rhom + Rinput` for `Rhom = {0}`: `Rinput` is the point
`c * (exp (a * r) - 1) / a` widened by `w`. -/
noncomputable def LinParamSys.firstTimeIntervalCora (a c r w : ℝ) : Set ℝ :=
  Set.Icc (c * (Real.exp (a * r) - 1) / a - w) (c * (Real.exp (a * r) - 1) / a + w)

/-- The state of `ẋ = -x + 1`, `x(0) = 0`. -/
noncomputable def LinParamSys.offsetState (t : ℝ) : ℝ := 1 - Real.exp (-t)

/-- `offsetState` solves `ẋ = -x + 1`. -/
theorem LinParamSys.offsetState_hasDerivAt (t : ℝ) :
    HasDerivAt LinParamSys.offsetState (-LinParamSys.offsetState t + 1) t := by
  unfold LinParamSys.offsetState
  exact (((hasDerivAt_neg t).exp).const_sub 1).congr_deriv (by ring)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The start state `x(0) = 0` is not in the set of the first step, for every `r` and every
width `w` below the end state `1 - e^{-r}`. -/
theorem LinParamSys.firstTimeIntervalCora_counterexample (r w : ℝ)
    (hw : w < LinParamSys.offsetState r) : -- --- STMT ---
    LinParamSys.offsetState 0 = 0 ∧
      LinParamSys.offsetState 0 ∉
        LinParamSys.firstTimeIntervalCora (-1) 1 r w := by -- --- PROOF ---
  have h0 : LinParamSys.offsetState 0 = 0 := by simp [LinParamSys.offsetState]
  refine ⟨h0, ?_⟩
  rw [h0]
  intro h
  have hP : 1 * (Real.exp (-1 * r) - 1) / -1 = LinParamSys.offsetState r := by
    unfold LinParamSys.offsetState
    ring_nf
  simp only [LinParamSys.firstTimeIntervalCora, Set.mem_Icc, hP] at h
  linarith [h.1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
