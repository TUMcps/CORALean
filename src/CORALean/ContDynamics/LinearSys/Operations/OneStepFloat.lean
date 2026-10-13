import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContSet.Zonotope.Float.Operations.Point

/-!
# `LinearSys.oneStepFloat`

`LinearSys.oneStep` [1, Sec. 3.3] computed in `𝕋`, one `let` per `let` of the real one: the
exact `e^{AΔt}` becomes `expIntervalFloat` at the point range `[Δt, Δt]`; `PU` and `Pu` are
`inputSolutionFloat` at `U` and at the point zonotope `{u}`; `[F]` and `[G]` are
`MatExp.intervalCorrectionMatrix` and `MatExp.intervalConstCorrectionMatrix` at the point box
of the stored `A`. Every product is `Zonotope.mtimesIntervalMat`, so rounding stays in the error
box.

`Δt` is a float and its own value is the step: nothing rounds the time here.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `oneStep`, one block, in floats: the time-point set `Rtp` and the time-interval set
`Rti` of the step `Δt`, from `X`, under the constant input `u` and the inputs in `U`, at Taylor
order `η`. -/
def LinearSys.oneStepFloat (sys : LinearSys 𝕋 n) (X U : Zonotope (Vec 𝕋 n)) (u : Vec 𝕋 n) (Δt : 𝕋)
    (η : ℕ) : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) :=
  let A := Interval.point sys.A                                           -- [A, A]
  let PU := sys.inputSolutionFloat Δt η U                                 -- time-varying input
  let Pu := sys.inputSolutionFloat Δt η (Zonotope.point u)                -- constant input
  let C_input := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- `[G] u`
    (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalConstCorrectionMatrix A Δt η) (Zonotope.point u)
  let Htp := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- `[e^{AΔt}] X ⊕ Pu`
    (S := fun k => Zonotope (Vec 𝕋 k))
    (sys.expIntervalFloat Δt Δt η) X ⊞ Pu
  let C_state := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- `[F] X`
    (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalCorrectionMatrix A Δt η) X
  let Hti := LinComb.linComb X Htp ⊞ C_state                              -- `CH(X, Htp) ⊕ C_state`
  (Htp ⊞ PU, Hti ⊞ PU ⊞ C_input)                                          -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
