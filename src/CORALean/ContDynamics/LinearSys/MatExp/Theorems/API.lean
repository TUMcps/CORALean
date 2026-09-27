import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsConstCorrectionMatrixLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrectionMatrixLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemInputCorrectionSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemStateCorrectionSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemSum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsParticularTailEntryLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AffineDynamicsErrorIsBigO
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AffineDynamicsErrorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AffineDynamicsErrorNonneg
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ErrorConvergesToZeroHomogeneousRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ErrorConvergesToZeroParticularRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsAffineDynamicsErrorLeConstMul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsExpRemainderBoundLt
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulExpRemainderBoundLt
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionErrorLeConstMulSq
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionTauErrorLeConstMul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureContainsExact
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureExact
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorExact
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWAttained
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWOuter
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundAntitoneSucc
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundSuperlinear
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatIsBigO
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderOrderLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderOrderSpec
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderStepSpec
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorTwo
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpWApply
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialDownFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialMulPowLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialUpFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HausdorffDist2AffineDynamicsLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HausdorffDist2ParticularSolutionLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IsBoundedParticularRemainderSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulMemMinmax
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralSubTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralTermLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularRemainderSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuterCorrelated
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularRemainderErrorSuperlinear
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionErrorIsBigO
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionErrorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionTauErrorIsBigO
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionTauErrorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowDownFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowSubEq
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermAttained
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermBetween
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RemainderEntryLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScalarTermLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SubLeZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SumExpTail2Le
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SumExpTailLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableNormExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SuperlinearDecreaseExpRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SuperlinearDecreaseExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoAffineDynamicsErrorZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundAtTop
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoMulExpRemainderBoundZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoParticularSolutionErrorZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoParticularSolutionTauErrorZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumLeExpTail
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq

/-!
# What the exponential enclosures guarantee

That `e^{Ar}` lies in `expEnclosure`, that the two interpolation errors lie in
the correction matrices, and that the integrated series converges. Each holds
only under `‖A‖r / (η + 2) < 1`. `ExpIntervalTaylor`/`ExpIntervalEnclosure` are
the same two facts widened to every member of an interval matrix, the second
checkable from the interval matrix alone via its `absMax`, and
`IntervalCorrectionMatrix`/`IntervalConstCorrectionMatrix`/`IntervalInputRemainder`
are the corresponding three for a step's two correction matrices and input
remainder. `ExpMatZonoEnclosure` is the same guarantee for a matrix zonotope,
checkable from the zonotope alone through the interval matrix it encloses.
`TendstoExpRemainderBoundAtTop`/`ExistsExpRemainderBoundLt` and
`TendstoMulExpRemainderBoundZero`/`ExistsMulExpRemainderBoundLt` are the limits adaptive
parameter tuning rests on: the bound vanishes as the order grows or the step shrinks.
`ExpRemainderBoundAntitoneSucc` says one more order never costs precision, and
`ExpRemainderOrderSpec`/`ExpRemainderOrderLe`/`ExpRemainderStepSpec` say the parameter
chosen for an admissible error meets it, the order least of those.
`TendstoExpRemainderMatZero`/`ExpRemainderMatIsBigO` are the same two limits at the entrywise
`ExpRemainderMat`, as `Lemma 2`'s and `Lemma 4`'s pairs are for `Δε^U_k`/`Δε^{U,τ}_k`; at it,
`SuperlinearDecreaseExpRemainderMat`, `ErrorConvergesToZero*RemainderError` and
`ParticularRemainderErrorSuperlinear` are CDC 2020's `Lemma 1`, `Prop. 3`/`4` and `Thm. 2`.
`ExpTaylorSmulMulVec`, `ContinuousExpDiff` and `RemainderEntryLe` serve an input solution, and
`HausdorffDist2ParticularSolutionLe`/`HausdorffDist2AffineDynamicsLe` are eqs. (25) and (23).
-/
