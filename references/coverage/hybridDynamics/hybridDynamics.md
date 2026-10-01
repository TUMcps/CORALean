# hybridDynamics/@hybridDynamics

CORA methods of `hybridDynamics/@hybridDynamics/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** none.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `hybridDynamics` | — | — |  |
| `verify` | proved | [`HybridAutomaton.holds_of_check`](../../../src/CORALean/HybridDynamics/Theorems/HoldsOfCheck.lean), [`HybridAutomaton.holds_of_invariant`](../../../src/CORALean/HybridDynamics/Theorems/HoldsOfRun.lean) | a `true` from `Specification.check` on the invariant implies the specification on the state every run ends in (true implies safe); checked on the location invariant, not on a computed reachable set as CORA's `verify` does |
