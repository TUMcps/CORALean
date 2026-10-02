# hybridDynamics/@linearReset

CORA methods of `hybridDynamics/@linearReset/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** none.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `evaluate` | float | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) · float: [`Transition.jumpFloat`](../../../src/CORALean/HybridDynamics/Operations/JumpFloat.lean), [`Transition.jumpFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuter.lean) | no input matrix B (CORA's linearReset has one; the Lean reset is `x ↦ Wx + w`); the reset applied to a state set |
| `eye` | float | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) · float: [`Transition.jumpFloat`](../../../src/CORALean/HybridDynamics/Operations/JumpFloat.lean), [`Transition.jumpFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuter.lean) | route a — the float twin of the reset applied to a state set; no input matrix B (CORA's linearReset has one; the Lean reset is `x ↦ Wx + w`) ; `eye` is `W = 1`, `w = 0` |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `lift` | — | — |  |
| `linearReset` | float | [`Transition.reset`](../../../src/CORALean/HybridDynamics/Definitions/Transition.lean), [`Transition.reset_image_subset`](../../../src/CORALean/HybridDynamics/Theorems/ResetImageSubset.lean) · float: [`Transition.jumpFloat`](../../../src/CORALean/HybridDynamics/Operations/JumpFloat.lean), [`Transition.jumpFloat_outer`](../../../src/CORALean/HybridDynamics/Theorems/JumpFloatOuter.lean) | route a — the float twin of the reset applied to a state set; no input matrix B (CORA's linearReset has one; the Lean reset is `x ↦ Wx + w`) |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `nonlinearReset` | — | — |  |
| `resolve` | — | — |  |
| `synchronize` | — | — |  |
