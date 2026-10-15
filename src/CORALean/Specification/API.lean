module

public import CORALean.Specification.AtomicProposition.API
public import CORALean.Specification.Definitions.API
public import CORALean.Specification.Instances
public import CORALean.Specification.FourValued.API
public import CORALean.Specification.FiniteKleeneSignalBuilder.API
public import CORALean.Specification.FiniteSignal.API
public import CORALean.Specification.FourValuedSignal.API
public import CORALean.Specification.FourValuedSTL.API
public import CORALean.Specification.Kleene.API
public import CORALean.Specification.KleeneSignal.API
public import CORALean.Specification.PointSegmentSignal.API
public import CORALean.Specification.ReachSetAnalyzer.API
public import CORALean.Specification.Rtl.API
public import CORALean.Specification.OnlineAnalyzerNode.API
public import CORALean.Specification.OnlineReachSetAnalyzer.API
public import CORALean.Specification.Operations.API
public import CORALean.Specification.Specification
public import CORALean.Specification.STL.API
public import CORALean.Specification.STLInterval.API
public import CORALean.Specification.SyntaxTree.API
public import CORALean.Specification.TentativeKleeneSignal.API
public import CORALean.Specification.TrajectoryAnalyzer.API
public import CORALean.Specification.Theorems.API
public import CORALean.Specification.Counterexamples.API

/-!
# Specifications, collected

What a requirement is in `Specification`, and what checking one buys in
`Theorems`. Its set is any representation, a plain `Set` among them; `Check` asks
it about a computed set through `Contains`/`IsDisjoint`, which `Instances`
computes at float boxes, zonotopes and halfspace descriptions, over any scalar.
`VerifyHalfspace` and `VerifyConvex` are the two
algorithms here, `[1, Alg. 2]`'s and `[1, Alg. 3 (exits)]`'s decision procedures — the
first in `Operations`, the second in `Definitions` beside its two soundness
theorems — and both have more soundness proved in `Theorems`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/
