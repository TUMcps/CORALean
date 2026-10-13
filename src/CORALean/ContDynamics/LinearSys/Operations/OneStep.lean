import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

/-!
# `LinearSys.oneStep`

CORA's `oneStep(linsys, X, U, u, Δt, η)`: one step under a constant input `u` and a time-varying
input set `U`, as the time-point set `Rtp` and the time-interval set `Rti` [1, Sec. 3.3]. One `let`
per CORA variable: `PU` is `inputSolution` at `U`; `Pu` is the same series at the singleton `{u}`,
which is CORA's `particularSolution_constant`; `C_input = G u` with `G` the constant input's
correction matrix; `Htp = e^{AΔt} X ⊕ Pu`; `C_state = F X`; `Hti = CH(X, Htp) ⊕ C_state`.

`linComb` is taken where CORA says `enclose` (convex hull), as in `timeIntervalStep`. CORA's
block decomposition (`blocks`, default one block) is not carried.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `oneStep`, one block: the time-point set `Rtp` and the time-interval set `Rti` of the
step `Δt`, from `X`, under the constant input `u` and the inputs in `U`, at Taylor order `η`. -/
noncomputable def LinearSys.oneStep (sys : LinearSys 𝕋 n) (X U : S n) (u : Vec ℝ n) (Δt : ℝ)
    (η : ℕ) : S n × S n :=
  let A := toRealMat sys.A
  let PU : S n := sys.inputSolution Δt η U                                -- time-varying input
  let Pu : S n := sys.inputSolution Δt η (OfPoint.ofPoint u)              -- constant input
  let C_input : S n := Mtimes.mtimes (𝕄 := ℐ)                             -- `G u`
    (MatExp.constCorrectionMatrix A Δt η) (OfPoint.ofPoint u)
  let Htp : S n := Mtimes.mtimes (exp (Δt • A)) X ⊞ Pu                    -- `e^{AΔt} X ⊕ Pu`
  let C_state : S n := Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix A Δt η) X   -- `F X`
  let Hti : S n := LinComb.linComb X Htp ⊞ C_state                        -- `CH(X, Htp) ⊕ C_state`
  (Htp ⊞ PU, Hti ⊞ PU ⊞ C_input)                                         -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
