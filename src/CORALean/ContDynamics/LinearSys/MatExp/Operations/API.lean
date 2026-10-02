import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineDynamicsError
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineTimePointNext
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureExact
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorExact
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderOrder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderStep
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpW
import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialUpFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinus
import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalMulVecSet
import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSum
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuterCorrelated
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError
import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowDownFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHi
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLo
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.OrderTestFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.StepTestFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneStepFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrectionMatrix

/-!
# What enclosing a matrix exponential computes

Every declaration here is something an algorithm evaluates for its own next value: the
truncated series and its remainder bound (`ExpTaylor`, `ExpRemainderBound`, `ExpEnclosure`),
the correction and input-remainder matrices a continuous-time step needs
(`CorrectionMatrix`, `ConstCorrectionMatrix`, `InputRemainder`, `ExpIntegral`) and their
interval- and matrix-zonotope-widened counterparts (`Interval*`, `ExpMatZono*`), the curvature
enclosure and affine error a step folds in (`CurvatureEnclosure`, `AffineDynamicsError`,
`AffineTimePointNext`, `AffineTimeIntervalOuter`), the particular-solution outer
approximations `AutoTuneOrder` sweeps against (`ParticularSolutionOuter`,
`ParticularSolutionOuterCorrelated`, `ParticularSolutionError`, `ParticularSolutionTauError`),
and the two tuning knobs that pick an order or a step from an admissible error
(`ExpRemainderOrder`, `ExpRemainderStep`).
-/
