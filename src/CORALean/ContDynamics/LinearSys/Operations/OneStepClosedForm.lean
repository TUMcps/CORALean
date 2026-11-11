module

public import CORALean.ContDynamics.LinearSys.Definitions.StepSets
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionEntrywise

@[expose] public section

/-!
# `LinearSys.oneStepClosedForm`

CORA's `oneStep(linsys, X, U, u, Δt, η)` as the closed form it computes, one `let` per variable of
`oneStep.m`: `e^{AΔt}` as one matrix, the curvatures `F` and `G` and the input solutions, each with
the entrywise remainder `E(Δt,η)` of [1], and `H(t₁)` not reduced. `LinearSys.oneStep` takes the
scalar remainder bound of [2, Eq. 2], which needs `‖AΔt‖ < η + 2`; here nothing is asked of `η`.
Unlike CORA, which multiplies the constant input by `A⁻¹(e^{AΔt} - I)` for invertible `A`, `Pu` is
the Taylor form CORA takes for singular `A`, so no inverse is certified.

## Inputs
* `sys` – linear system
* `X` – start set
* `U` – input set
* `u` – constant input
* `Δt` – step length
* `η` – Taylor order

## Output
* time-point and time-interval sets of the step

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
* [2] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `oneStep`, one block, in closed form: the time-point set `Rtp` and the time-interval
set `Rti` of the step `Δt`, from `X`, under the constant input `u` and the inputs in `U`, at
Taylor order `η`. -/
noncomputable def LinearSys.oneStepClosedForm (sys : LinearSys 𝕋 n) (X U : S n) (u : Vec ℝ n)
    (Δt : ℝ) (η : ℕ) : LinearSys.StepSets (S n) :=
  let A := toRealMat sys.A
  let eAdt : Mat ℝ n n := exp (Δt • A)                                    -- `e^{AΔt}`
  let PU : S n := sys.inputSolutionEntrywise Δt η U                       -- time-varying input
  let Pu : S n := sys.inputSolutionEntrywise Δt η (OfPoint.ofPoint u)     -- constant input
  let G := MatExp.constCorrectionMatrixEntrywise A Δt η                   -- input curvature
  let C_input : S n := Mtimes.mtimes (𝕄 := ℐ) G (OfPoint.ofPoint u)      -- `G u`
  let Htp : S n := Mtimes.mtimes eAdt X ⊞ Pu                              -- `e^{AΔt} X ⊕ Pu`
  let F := MatExp.correctionMatrixEntrywise A Δt η                        -- state curvature
  let C_state : S n := Mtimes.mtimes (𝕄 := ℐ) F X                         -- `F X`
  let Hti : S n := LinComb.linComb X Htp ⊞ C_state                        -- `CH(X, Htp) ⊕ C_state`
  ⟨Htp ⊞ PU, Hti ⊞ PU ⊞ C_input⟩                                         -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
