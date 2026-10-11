import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
import CORALean.ContDynamics.LinearSys.Krylov.Operations.GramSchmidtStep

/-!
# The Arnoldi iteration

`Arnoldi` is Alg. 1 of Althoff (TAC 2020), its inner modified Gram–Schmidt sweep
`GramSchmidtStep`; `Augment` the matrix `[A u; 0 0]` of a constant input (Lemma IV.1).
-/
