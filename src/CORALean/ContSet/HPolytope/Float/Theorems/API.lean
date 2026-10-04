import CORALean.ContSet.HPolytope.Float.Theorems.ProjectHighDimExact
import CORALean.ContSet.HPolytope.Float.Theorems.IsequalNominal
import CORALean.ContSet.HPolytope.Float.Theorems.NotInner
import CORALean.ContSet.HPolytope.Float.Theorems.BoundOfDualLe
import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Float.Theorems.PlusOfOuter
import CORALean.ContSet.HPolytope.Float.Theorems.LinCombOfOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MtimesOfOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MinusOuter
import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner
import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet
import CORALean.ContSet.HPolytope.Float.Theorems.CartProdExact
import CORALean.ContSet.HPolytope.Float.Theorems.OriginExact
import CORALean.ContSet.HPolytope.Float.Theorems.LiftExact
import CORALean.ContSet.HPolytope.Float.Theorems.RepresentsaFullspaceSound
import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos
import CORALean.ContSet.HPolytope.Float.Theorems.ReduceOverDomainRows
import CORALean.ContSet.HPolytope.Float.Theorems.ReduceOverDomainOuter
import CORALean.ContSet.HPolytope.Float.Theorems.ReduceOverDomainInner

/-!
# What the float `HPolytope` guarantees

The certified operations enclose, each in one line: the rounding was paid inside
the bound composition, so no proof here mentions it. The exact operations state
their own guarantee next to their definition, having none to compose, and
`MemConstruct` is the reading of the stored rows they all state it in.
-/
