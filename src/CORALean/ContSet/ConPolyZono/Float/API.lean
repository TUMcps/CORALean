module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.API
public import CORALean.ContSet.ConPolyZono.Float.Theorems.API
public import CORALean.ContSet.ConPolyZono.Float.Instances

/-!
# Constrained polynomial zonotopes over a floating-point scalar, collected

The representation and its error box in `ConPolyZono`, the operations in
`Operations`, their guarantees in `Theorems`, and the operation instances in
`Instances` — the `InflatedContSet` one is in `ConPolyZono`, being what the
error box means.

The representation's docstring is where to read where a float operation may pay:
into the ambient error box, as everywhere else, and — this representation alone —
into the interval a constraint's right-hand side is. `intersection` is the
operation that needs both at once, and the one this representation exists for.
-/
