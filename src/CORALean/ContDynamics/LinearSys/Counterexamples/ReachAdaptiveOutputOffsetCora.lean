module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearSys.adaptiveOutputOffsetCora`: the output offset of the next input piece

For a piecewise-constant input (`params.uTransVec` with the switching times `params.tu`),
`canonicalForm` returns `vTransVec = D * [uTransVec, 0] + k + ...`, one column per input piece and
a last column for the time after the final piece. `priv_reach_adaptive.m` reads, for a step that
starts in piece `idx = find(t >= tu, 1, 'last')`, the input `uTrans = uTransVec(:,idx)` but
`vTrans = vTransVec(:,idx+1)` (l. 648-661, the comment says the time-point set needs the next
column), and `aux_outputset` (l. 667-752) adds this one `vTrans` to the time-interval set and to the
time-point set of the step. Every step is limited to a piece (`aux_maxTimeStep`, l. 1059-1076), so
in a step inside piece `idx` the output carries `D * u_{idx+1}`, and in the last piece `0`, where
the input is `u_idx` (`priv_reach_standard` takes `v(:,k)` for the time interval and `v(:,k+1)` for
the time point). Modelled in `ℝ`, with 0-based pieces: `vVec j` is column `j + 1`. Read from the
source, not run.

# CORA's adaptive `reach` uses the offset of the next input piece

`linearSys(-1,1,0,1,1)` (`ẋ = -x + u`, `y = x + u`), `R0 = {0}`, `uTransVec = [0 1]`,
`tu = [0 1]`, `tFinal = 2`: `vTransVec = [0 1 0]`. In `[0, 1)` the input is `0`, so `x = 0` and
`y = 0`; the first output set is `x + vTransVec(:,2) = {1}` (all error generators are zero here).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `vTrans = vTransVec(:,idx+1)` of a step in piece `piece` (0-based). -/
def LinearSys.adaptiveVTransCora (vVec : Nat → ℝ) (piece : Nat) : ℝ :=
  vVec (piece + 1)

/-- The offset `D * u + k` of the piece itself. -/
def LinearSys.pieceOffset (vVec : Nat → ℝ) (piece : Nat) : ℝ :=
  vVec piece

/-- The input offsets `D * [0 1 0]` of the witness. -/
def LinearSys.witnessVVec : Nat → ℝ := fun j => if j = 1 then 1 else 0


-- =======================================  MAIN THEOREM  ======================================= --

/-- In piece `0` the output is `x + 0 = 0` for `x = 0`, and CORA's set is `{0 + 1}`; in piece `1`
it is `x + 1` and CORA adds `0`. -/
theorem LinearSys.adaptiveVTransCora_counterexample :
    LinearSys.pieceOffset LinearSys.witnessVVec 0 = 0 ∧
      LinearSys.adaptiveVTransCora LinearSys.witnessVVec 0 = 1 ∧
      (0 : ℝ) ∉ ({0 + LinearSys.adaptiveVTransCora LinearSys.witnessVVec 0} : Set ℝ) ∧
      LinearSys.pieceOffset LinearSys.witnessVVec 1 = 1 ∧
      LinearSys.adaptiveVTransCora LinearSys.witnessVVec 1 = 0 := by -- --- PROOF ---
  simp [LinearSys.pieceOffset, LinearSys.adaptiveVTransCora, LinearSys.witnessVVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
