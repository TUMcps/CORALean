module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.GramSchmidtStep
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Alg2
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Alg2Corrected
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ReachKrylovCora1D

/-!
# The Arnoldi iteration

`Arnoldi` is Alg. 1 of Althoff (TAC 2020), its inner modified Gram–Schmidt sweep
`GramSchmidtStep`, and its output as the matrices `ArnoldiBasis` (`V`) and `ArnoldiHessenberg`
(`H`); `Augment` the matrix `[A u; 0 0]` of a constant input (Lemma IV.1). `Alg2` is Alg. 2 as
printed, over its subroutines' outputs, and `Alg2Corrected` the same with lines 8 and 10 repaired.
`ReachKrylovCora1D` is CORA's first `'krylov'` time-point set in 1D, as printed.
-/
