import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
import CORALean.ContDynamics.LinearSys.Krylov.Operations.GramSchmidtStep
import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg

/-!
# The Arnoldi iteration

`Arnoldi` is Alg. 1 of Althoff (TAC 2020), its inner modified Gram–Schmidt sweep
`GramSchmidtStep`, and its output as the matrices `ArnoldiBasis` (`V`) and `ArnoldiHessenberg`
(`H`); `Augment` the matrix `[A u; 0 0]` of a constant input (Lemma IV.1).
-/
