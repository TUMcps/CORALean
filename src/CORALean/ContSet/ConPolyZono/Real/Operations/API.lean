import CORALean.ContSet.ConPolyZono.Real.Operations.And
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.Map
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap

/-!
# What `ConPolyZono` computes

`and`, `plus`, `map` and `quadMap` exactly, and `dependent`, which moves the
independent block into the dependent one and is what makes both `and` and
`quadMap` exact rather than merely sound.

`and` is the one to read: everything else a polynomial zonotope already
computes, and this is what the constraints buy.

`quadMap` carries over from `PolyZonotope` unchanged, and that it does is worth
knowing — a quadratic map reads the generators and the exponent matrix, and the
constraints read neither, so they pass through and constrain the image exactly
as they constrained the argument.

No `linComb` and no `reduce`; `Instances` says why.
-/
