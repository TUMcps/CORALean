module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.CorrectionSet
public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.SubspaceFloat

/-!
# What the Krylov enclosures are held to

`CorrectionSet` is Lemma III.3's correction interval matrix, as the set of matrices it holds;
`SubspaceFloat` the Krylov subspace the float order search returns, `LyapunovCertificateFloat` the
weight, bounds and rate of the float Lyapunov check.
-/
