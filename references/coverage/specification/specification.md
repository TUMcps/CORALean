# specification/@specification

CORA methods of `specification/@specification/` (a class of `specification/` or `specification/signals/`; a single-file class lists its public methods, constructor included), one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Specification` (the structure, with the kinds `safeSet`, `unsafeSet`, `invariant`; `custom` is a plain `Set`) and `Specification.check`. `'logic'` specifications (signal temporal logic) are the `stl` class; their checking is not here.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `add` | — | — |  |
| `check` | float | [`Specification.check`](../../../src/CORALean/Specification/Operations/Check.lean), [`Specification.check_sound`](../../../src/CORALean/Specification/Theorems/CheckSound.lean) | route b — generic over the representation of the specification's set and of the checked set (the `Contains` and `IsDisjoint` instances), computable; a `true` implies the specification on the set (`check_sound`), `false` claims nothing; safe sets, unsafe sets and invariants, not `'logic'`; cora-issue — the custom branch `aux_checkCustom` (l. 319-333) on a cell of sets returns `true` as soon as any piece passes `func`, where the sibling branches need every piece to pass, so a custom specification that one parallel set violates is reported satisfied ([`Specification.checkCustomCora`](../../../src/CORALean/Specification/Operations/CheckCustomCora.lean), [`Specification.checkCustomCora_any_counterexample`](../../../src/CORALean/Specification/Theorems/CheckCustomCoraAnyCounterexample.lean); [FINDINGS](../../../FINDINGS.md), "Specification `check`, custom specification on a cell") |
| `eq` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `inverse` | — | — |  |
| `isempty` | — | — |  |
| `isequal` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `ne` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plotOverTime` | out-of-scope | n/a — plotting/display |  |
| `printSpec` | out-of-scope | n/a — plotting/display |  |
| `project` | — | — |  |
| `robustness` | — | — | definition only, no theorem: [`Specification.distancePolyPointCora`](../../../src/CORALean/Specification/Operations/DistancePolyPointCora.lean) models `aux_distancePolyPoint` as printed, not the whole method; cora-issue — `aux_distancePolyPoint` (l. 189-224) values a point outside the set by the Euclidean distance with one or `n` violated rows but by the norm 1 distance otherwise, so the magnitude is not monotone (the sign is right) ([`Specification.distancePolyPointCora_norm_counterexample`](../../../src/CORALean/Specification/Theorems/DistancePolyPointCoraNormCounterexample.lean); [FINDINGS](../../../FINDINGS.md), "Specification `robustness`, `aux_distancePolyPoint` mixes norms") |
| `specification` | float | [`Specification`](../../../src/CORALean/Specification/Specification.lean), [`Specification.holds_of_outer`](../../../src/CORALean/Specification/Theorems/HoldsOfOuter.lean), [`Specification.holds_safeSet_of_bounds`](../../../src/CORALean/Specification/Theorems/Containment.lean) | route b (scalar-free) — the structure holds a set of any representation and a kind, no scalar of its own, and is computable; `holds_of_outer` is stated for every representation: the structure (a set in any representation and a kind: `safeSet`, `unsafeSet`, `invariant`) and its denotation `Specification.Holds`, with the theorem that a verdict on an outer approximation carries over to the exact set (`holds_of_outer`); `custom` is a plain `Set`, `logic` (STL) is not a `Specification` (see the `stl` table); the argument parsing, the `time` and `location` fields and the `'logic'` type are not modelled |
| `splitLogic` | — | — |  |
