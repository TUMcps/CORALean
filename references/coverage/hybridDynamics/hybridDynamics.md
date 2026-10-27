# hybridDynamics/@hybridDynamics

CORA methods of `hybridDynamics/@hybridDynamics/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** none.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `hybridDynamics` | out-of-scope | n/a — matlab-runtime | abstract class constructor: stores only dimensions and a name, which are type indices in Lean |
| `verify` | float | [`HybridAutomaton.holds_of_check`](../../../src/CORALean/HybridDynamics/Theorems/HoldsOfCheck.lean), [`HybridAutomaton.holds_of_isInvariant`](../../../src/CORALean/HybridDynamics/Theorems/HoldsOfRun.lean), [`Specification.check`](../../../src/CORALean/Specification/Operations/Check.lean), [`Specification.check_sound`](../../../src/CORALean/Specification/Theorems/CheckSound.lean) | route b — `holds_of_check` is generic over `Scalar 𝕋` and the set representations, `Specification.check` is a computable Bool; instantiated at the float zonotope and halfspace as in `Examples/ReachFloat.lean`. A `true` from `Specification.check` on the invariant implies the specification on the state every run ends in (true implies safe); checked on the location invariant, not on a computed reachable set as CORA's `verify` does |
