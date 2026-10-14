# contSet/@affine

CORA methods of `contSet/@affine/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Taylm` at order one (`Interval.taylm` at `N = 1`): CORA's `affine` is a subclass of `taylm`, built with `max_order = 1` (R-AFF).

| Method | State | In CORALean | Note |
|---|---|---|---|
| `affine` | float | [`Interval.taylm`](../../../src/CORALean/ContSet/Conversion/Real/Operations/Interval_to_Taylm.lean), [`Interval.taylm_exact`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean), [`Interval.taylm_contains`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean) · float: [`Interval.taylm`](../../../src/CORALean/ContSet/Conversion/Float/Operations/Interval_to_Taylm.lean), [`Interval.taylm_contains`](../../../src/CORALean/ContSet/Conversion/Float/Interval_to_Taylm.lean) | R-AFF: CORA's `affine` is a Taylor model of order one (`classdef affine < taylm`, built as `taylm(int, 1, ...)`), so the constructor is `Interval.taylm` at `N = 1`: one model `mid + rad · tᵢ` per coordinate, no remainder; exact at ℝ for a nonempty box; float: outer only (the float models' range contains the box); variable names are positional indices, and CORA's `opt_method`, `eps` and `tolerance` are not modelled |
