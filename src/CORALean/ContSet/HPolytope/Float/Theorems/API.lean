import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Float.Theorems.PlusOfOuter
import CORALean.ContSet.HPolytope.Float.Theorems.LinCombOfOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MtimesOfOuter

/-!
# What the float `HPolytope` guarantees

The certified operations enclose, each in one line: the rounding was paid inside
the bound composition, so no proof here mentions it. The exact operations state
their own guarantee next to their definition, having none to compose, and
`MemConstruct` is the reading of the stored rows they all state it in.
-/
