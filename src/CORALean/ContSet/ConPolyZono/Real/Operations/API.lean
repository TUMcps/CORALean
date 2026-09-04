import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.ConPolyZono.Real.Operations.And
import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.Map
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap

/-!
# What `ConPolyZono` computes

`and`, `plus`, `map`, `quadMap` and `compact` exactly, and `dependent`, which
moves the independent block into the dependent one and is what makes both `and`
and `quadMap` exact rather than merely sound.

`and` is the one to read: everything else a polynomial zonotope already
computes, and this is what the constraints buy.

`compact` is the one that has to know about the sharing. Merging is
`PolyZonotope`'s at both blocks, but a factor is dropped only when neither `E`
nor `EC` reads it, so the two exponent matrices are dropped from together.

`quadMap` carries over from `PolyZonotope` unchanged, and that it does is worth
knowing — a quadratic map reads the generators and the exponent matrix, and the
constraints read neither, so they pass through and constrain the image exactly
as they constrained the argument.

`PadE` and `AppendE` are the two ways a constraint block is reshaped — widened
by factors it does not read, and set beside another over the same factors.

No `linComb` and no `reduce`; `Instances` says why.
-/
