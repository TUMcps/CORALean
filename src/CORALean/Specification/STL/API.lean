module

public import CORALean.Specification.STL.Definitions.API
public import CORALean.Specification.STL.Operations.API
public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.API
public import CORALean.Specification.STL.Counterexamples.API

/-!
# Signal temporal logic model checking, collected

`STL` is signal temporal logic over traces, `Definitions` the reachset temporal logic RTL over
reach sequences, `Operations` the transformation `Υ` between them on a normal form, and
`Theorems` the results of [1, Lemma 2] and [1, Table 1] about it: `Υ` is sound and complete for
c-divisible reach sequences (`STL.CNF.upsilon_sound_complete`), and the rewriting rules that bring a
general formula there.

Not here: the rewriting to sampled time as an algorithm, the conversion to normal form, and the
end-to-end model checking `Thm. 1`; `references/2016/roehm-atva-stl-model-checking.md` says which.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/
