module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.AffineDynamicsErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.AffineTimeIntervalSolution
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpDiffMatrices
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.HomogeneousRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.OrderAdmissible
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionTauErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.StepAdmissible
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.PeanoBakerInputTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.DependentTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpmMixed

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
