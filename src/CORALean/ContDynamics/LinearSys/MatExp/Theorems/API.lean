import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

/-!
# What the exponential enclosures guarantee

That `e^{Ar}` lies in `expEnclosure`, that the two interpolation errors lie in
the correction matrices, and that the integrated series converges. Each holds
only under `‖A‖r / (η + 2) < 1`.
-/
