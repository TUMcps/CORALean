import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceOuter

/-!
# What the float `ConZonotope` guarantees

Each operation encloses what the exact one does. The constraints cost nothing to
carry through `plus`: padding is exact, so the only rounding is the centre's and
the box absorbs it exactly as a zonotope's does. `MemNominalSet` is how each of
them reads the nominal half of a point.
-/
