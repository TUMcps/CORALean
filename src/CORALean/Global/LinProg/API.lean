module

public import CORALean.Global.SupportFunction.SupportFunction
public import CORALean.Global.LinProg.Duality
public import CORALean.Global.SupportFunction.Composition
public import CORALean.Global.LinProg.Simplex
public import CORALean.Global.LinProg.Farkas

/-!
# Linear programming, collected

The LP machinery behind the bounds of `Global/SupportFunction`: `Duality` produces
a `SupportBound` from a solver's dual solution (weak duality), `Farkas` characterizes
infeasibility and containment of polytopes, and `Simplex` is the solver — unverified,
and the one thing here nothing else relies on being right.
-/
