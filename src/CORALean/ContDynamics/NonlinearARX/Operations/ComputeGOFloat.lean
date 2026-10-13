import CORALean.ContDynamics.NonlinearARX.Operations.FeedFloat
import CORALean.ContDynamics.NonlinearARX.Operations.FloatJacModelToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGOFloat
import CORALean.ContSet.Interval.Float.Operations.Mtimes

/-!
# `NonlinearARX.computeGOFloat`

CORA's `nonlinearARX/computeGO` [1] with `compute_params = true`, as `computeGO` but over `𝕋`:
`NonlinearSysDT.computeGOFloat` of the converted float model with Jacobians, whose Jacobians are
CORA's `A_tilde = [A_tilde_firstRows; A_lin]` and `B_tilde = [B_tilde_firstRows; B_lin]`, with
the selection matrix `outputSel` as the output equation (`C_tilde`: its value is `mtimes`, its
Jacobians the matrix itself and zero) and the stacked reference inputs `feedFloat p u_ref`
(`getStackedU`). Soundness is `computeGOFloat_outer`.

## References

* [1] `contDynamics/@nonlinearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters along the reference run from the window `x0` under `u_ref`, as intervals
enclosing `computeGO`'s. -/
def NonlinearARX.computeGOFloat (sys : NonlinearARX dy du p)
    (fm : NonlinearARX.FloatJacModel 𝕋 dy du p) (x0 : Vec 𝕋 (p * dy)) (u_ref : ℕ → Vec 𝕋 du) :
    NonlinearSysDT.GOFloat 𝕋 (p * dy) ((p + 1) * du) dy :=
  let nlnsysDT := fm.toNonlinearSysDTFloat                         -- nlnARX.nonlinearSysDT
  let u_stacked := NonlinearARX.feedFloat p u_ref                  -- getStackedU(nlnARX,u_ref)
  let C_tilde := sys.outputSel (𝕋 := 𝕋)                            -- C_tilde
  let out : NonlinearSysDT.FloatJacModel 𝕋 (p * dy) ((p + 1) * du) dy :=   -- y_d = C_tilde x_d
    ⟨fun X _ => Interval.mtimes C_tilde X, fun _ _ => Interval.point C_tilde,
      fun _ _ => Interval.point fun _ _ => zero⟩
  NonlinearSysDT.computeGOFloat nlnsysDT out x0 u_stacked

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
