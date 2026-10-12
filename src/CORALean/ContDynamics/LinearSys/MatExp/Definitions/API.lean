import CORALean.ContDynamics.LinearSys.MatExp.Definitions.AffineDynamicsErrorBound
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.AffineTimeIntervalSolution
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpDiffMatrices
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.HomogeneousRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.OrderAdmissible
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionErrorBound
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionTauErrorBound
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.StepAdmissible
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerTerm
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerInputTerm

/-!
# What enclosing a matrix exponential means

Error measures that only state a result, never something an algorithm computes: `ExpRemainderMat`
(the entrywise-sharper remainder `Theorems`' convergence rates use), `AffineDynamicsErrorBound`,
`ParticularSolutionErrorBound`/`ParticularSolutionTauErrorBound`, `ParticularRemainderError` and
`HomogeneousRemainderError` — CDC 2020's `ε_P`/`ε_H` of eq. (21)-(22) and the two correction sets
they are built from. `AffineTimeIntervalSolution` is the exact tube `affineTimeIntervalOuter`
encloses. `OrderAdmissible`/`StepAdmissible` are the two tuning knobs' admissibility specs.
`PeanoBakerTerm`/`PeanoBakerInputTerm` are the series of a matrix that varies in time.
-/
