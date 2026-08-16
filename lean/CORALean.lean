import CORALean.Global.API
import CORALean.ContSet
import CORALean.ContSet.Interval.Theorems
import CORALean.ContSet.Zonotope.Theorems

/-!
# CORALean

CORA's continuous set representations and their operations, over the reals.

Layout follows CORA's: `Global/` for `global/`, one directory per representation
under `ContSet/` for `contSet/@name`. Names are CORA's: `plus`, `mtimes`,
`reduce`, `interval`.

Per representation, `API` defines, `Theorems` states one guarantee per
operation, and `Proofs/` holds one file per proof.

Coefficients here are real. The floating-point layer refines this one along the
same `⊆`.
-/
