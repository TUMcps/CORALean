# contDynamics/@contDynamics

CORA methods of `contDynamics/@contDynamics/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Reach`, `OutputEq`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `conform` | — | — |  |
| `contDynamics` | — | — |  |
| `createTestSuite` | out-of-scope | n/a — random/sampling |  |
| `derivatives` | — | — |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | — | — |  |
| `isconform` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `linReach` | — | — | cora-issue — the check `R([iΔt,(i+1)Δt]) ⊆ R_i` is made on a set computed under the very confinement it checks, so it establishes nothing; CORALean takes confinement from an a priori ball about the step's start ([FINDINGS](../../../FINDINGS.md), "Confinement of a run to a linearization's region") |
| `linReachInner` | — | — |  |
| `observe` | — | — |  |
| `observe_stripBased` | — | — |  |
| `outputSet` | float | [`OutputEq.outputSet`](../../../src/CORALean/ContDynamics/OutputEq/Operations/OutputSet.lean), [`OutputEq.outputSet_outer`](../../../src/CORALean/ContDynamics/OutputEq/Theorems/OutputSetOuter.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `printSystem` | out-of-scope | n/a — plotting/display |  |
| `reach` | float | [`Reach`](../../../src/CORALean/ContDynamics/Reach/Reach.lean) | route b — the interface class is generic over the system and the representation; `LinearSysDT 𝕋` instantiates it at any scalar (`ContDynamics/LinearSysDT/Instances.lean`) |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `symVariables` | — | — |  |
| `verify` | — | — |  |
