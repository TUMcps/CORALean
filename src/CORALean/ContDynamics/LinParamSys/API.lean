import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinParamSys.Operations.API
import CORALean.ContDynamics.LinParamSys.Theorems.API

/-!
# Continuous-time linear systems with a set-valued system matrix, collected

The system and its two trajectory predicates, `Trajectory` and
`ConstTrajectory`, in `LinParamSys`; one step of the flow and of the input, at
every matrix the set holds, in `Operations`; the guarantees relating the two
readings and enclosing a run in `Theorems`.

Reachability is `'constParam'`, at `ℐ`, and over one step. `'constParam'`
because a member fixed over the step is what makes the flow a matrix
exponential at all; `ℐ` because the exponential of a matrix set and its
correction matrix are interval matrices; one step because the input's
enclosure is proved where the step ends, `LinearSys`'s extension to every time
inside it resting on `inputReach`, which is written at a point matrix only.
-/
