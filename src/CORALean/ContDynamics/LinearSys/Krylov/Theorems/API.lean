import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiRelation
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeLinear
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpAugmentMulVec
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpDiffMemCorrectionSet
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpMulIntervalSubset
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ImageSubsetOfApprox
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputSolutionMemBox
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InterpMemCorrection
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.MemBoxOfNormLe
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PartialInputSolutionCounterexample
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PartialInputSolutionMemBox
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PrintedTimeIntervalCounterexample
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.TimeIntervalSubset
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PowMulVecOfHessenberg
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiBasisMulVecPow
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentArnoldiPow
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ConvexKrylovTermSet
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputReachSubsetKrylovTaylor
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputReachSubsetSumExpImage
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PrintedInputPropagationCounterexample
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentPowMulVec
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.VaryingInputNotOfErrorBound

/-!
# What the Krylov reachability of Althoff (TAC 2020) guarantees

`MemBoxOfNormLe` turns the a-posteriori error bound into an error box (Lemma III.1), and
`ImageSubsetOfApprox` the per-vector boxes into a zonotope enclosure of a linear image
(Thm. III.1, Thm. IV.1). `ExpDiffMemCorrectionSet` and `InterpMemCorrection` are Lemma III.3,
at the reduced matrix `H` and then mapped back through `V`; `ExpMulIntervalSubset` is Lemma III.2,
`ArnoldiRelation` what Alg. 1 computes, and `ErrorLeLinear` Prop. B.1's error bound linear in time.
`TimeIntervalSubset` is Thm. III.2 with the `[-1, 1]` the printed `N` drops
(`PrintedTimeIntervalCounterexample`). `ExpAugmentMulVec` reads `∫₀ᵗ e^{Aσ}dσ u` off the augmented
exponential, which makes `InputSolutionMemBox` Lemma IV.1; `PartialInputSolutionMemBox` is Cor. IV.1
with the sum of the two error radii (`PartialInputSolutionCounterexample`).
`ArnoldiBasisMulVecPow` (through `PowMulVecOfHessenberg`) makes Alg. 1 exact below the Krylov
order, so `AugmentArnoldiPow` reads `P Ṽ H̃ʲ e₁ = A^{j-1}u`: the sets of Thm. IV.2 are convex there
(`ConvexKrylovTermSet`), and `InputReachSubsetKrylovTaylor` is Thm. IV.2's Taylor part for varying
inputs with the thesis' remainder; `VaryingInputNotOfErrorBound` shows that Thm. IV.2's own
remainder does not follow from the error bound (3) alone. `InputReachSubsetSumExpImage` is
Alg. 2's input part with (24)'s exponent, which line 8 overshoots
(`PrintedInputPropagationCounterexample`).
-/
