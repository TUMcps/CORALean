module

public import CORALean.Specification.FourValuedSTL.Counterexamples.API
public import CORALean.Specification.FourValuedSTL.Definitions.API
public import CORALean.Specification.FourValuedSTL.FourValuedSTL
public import CORALean.Specification.FourValuedSTL.Operations.API
public import CORALean.Specification.FourValuedSTL.Theorems.API

/-!
# Signal temporal logic with the strict until, collected

`FourValuedSTL` is STL over executions with the strict until of [1, Sec. 2.5]; `Definitions` holds
`â` of an atom, `H ⊨ φ`, the reachable set and the relations `ξ ≺ R`, `R ≺ R̃`; `Operations` the
satisfaction signals `⟦φ⟧_R` over `U₁` ([1, Sec. 4.2 (satisfaction)]) and `⟦φ⟧_R̃` over `U₂`
([1, Sec. 4.3 (satisfaction)]), built from the signal operators of `KleeneSignal` and
`FourValuedSignal`; `Theorems` the soundness theorems [1, Thm. 1] and [1, Thm. 2], the verdict
[1, Cor. 1], and the until of [1, Lemma 2 (STL)]; `Counterexamples` the system without executions
that [1, Cor. 1] does not cover.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/
