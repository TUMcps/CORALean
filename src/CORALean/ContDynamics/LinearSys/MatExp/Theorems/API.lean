import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialMulPowLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulMemMinmax
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowSubEq
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScalarTermLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SubLeZero
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableNormExpIntegral

/-!
# What the exponential enclosures guarantee

That `e^{Ar}` lies in `expEnclosure`, that the two interpolation errors lie in
the correction matrices, and that the integrated series converges. Each holds
only under `‖A‖r / (η + 2) < 1`. `ExpIntervalTaylor`/`ExpIntervalEnclosure` are
the same two facts widened to every member of an interval matrix, the second
checkable from the interval matrix alone via its `absMax`.
-/
