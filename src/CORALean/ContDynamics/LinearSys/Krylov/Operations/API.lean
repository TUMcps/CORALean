module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.GramSchmidtStep
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Alg2
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Alg2Corrected
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ResidualNormFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.DecayProductFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.StartErrorFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.OrderOkFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.SubspaceFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowsFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorOkFloat

/-!
# The Arnoldi iteration

`Arnoldi` is Alg. 1 of Althoff (TAC 2020), its inner modified Gram–Schmidt sweep
`GramSchmidtStep`, and its output as the matrices `ArnoldiBasis` (`V`) and `ArnoldiHessenberg`
(`H`); `Augment` the matrix `[A u; 0 0]` of a constant input (Lemma IV.1). `Alg2` is Alg. 2 as
printed, over its subroutines' outputs, and `Alg2Corrected` the same with lines 8 and 10 repaired.
`ArnoldiFloat` is Alg. 1 in floats, `ResidualNormFloat` the
bound of what the stored basis leaves in the Krylov identity, `QuadBoundUp` Gershgorin's bound of
the quadratic form, `ErrorBoundFloat` the computable error bound for every matrix built from
them,
`OrderOkFloat` its test and `SubspaceFloat` the order search that uses it; `WindowsFloat` the
time-interval sets of the subspace.
`LyapunovCertificateFloat` checks a weight `P` for which `e^{tA}` decays in the weighted norm and
`RestartedErrorBoundFloat` accumulates the windows' errors in it (`RestartedErrorOkFloat` tests it),
for a stable non-normal `A` whose Gershgorin bound `QuadBoundUp` is large.
`ReachKrylovCora1D` is CORA's first `'krylov'` time-point set in 1D, as printed.
-/
