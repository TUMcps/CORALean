import CORALean.ContSet.ZonoBundle.Real.Operations.Box
import CORALean.ContSet.ZonoBundle.Real.Operations.DirBox
import CORALean.ContSet.ZonoBundle.Real.Operations.DirFil
import CORALean.ContSet.ZonoBundle.Real.Operations.DirFlow
import CORALean.ContSet.ZonoBundle.Real.Operations.DirPca
import CORALean.ContSet.ZonoBundle.Real.Operations.DirPcaCovariance
import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingBox
import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalAll
import CORALean.ContSet.ZonoBundle.Real.Operations.FacetLift
import CORALean.ContSet.ZonoBundle.Real.Operations.FlowIndex
import CORALean.ContSet.ZonoBundle.Real.Operations.GuardIntersect
import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
import CORALean.ContSet.ZonoBundle.Real.Operations.Map
import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
import CORALean.ContSet.ZonoBundle.Real.Operations.Parallelotope
import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.ZonoBundle.Real.Operations.Pool
import CORALean.ContSet.ZonoBundle.Real.Operations.Replace
import CORALean.ContSet.ZonoBundle.Real.Operations.QuadMap
import CORALean.ContSet.ZonoBundle.Real.Operations.Empty
import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
import CORALean.ContSet.ZonoBundle.Real.Operations.ReduceCombined
import CORALean.ContSet.ZonoBundle.Real.Operations.Shrink
import CORALean.ContSet.ZonoBundle.Real.Operations.Split
import CORALean.ContSet.ZonoBundle.Real.Operations.SupportBound
import CORALean.ContSet.ZonoBundle.Real.Operations.Project
import CORALean.ContSet.ZonoBundle.Real.Operations.CartProd
import CORALean.ContSet.ZonoBundle.Real.Operations.Enlarge
import CORALean.ContSet.ZonoBundle.Real.Operations.Isequal
import CORALean.ContSet.ZonoBundle.Real.Operations.IsequalCora
import CORALean.ContSet.ZonoBundle.Real.Operations.AllMembersFullDim
import CORALean.ContSet.ZonoBundle.Real.Operations.IsCentre
import CORALean.ContSet.ZonoBundle.Real.Operations.ContainsAll
import CORALean.ContSet.ZonoBundle.Real.Operations.IsIntervalCora
import CORALean.ContSet.ZonoBundle.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTight
import CORALean.ContSet.ZonoBundle.Real.Operations.ConvHull
import CORALean.ContSet.ZonoBundle.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightPoints
import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVertices
import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVerticesNonempty

/-!
# What a zonotope bundle computes, collected

`intersection`, exact and the whole point of the representation; `plus`, `linComb`,
`mtimes` and `mtimesMatZonotope`, all enclosures over the family, one component
at a time; `map`, one
linear image per component, which `Instances` reads at a bijective one for
`Reindex`; and `ofPoint`, a bundle of one point-zonotope. `supportBound`
answers a direction without a linear program, taking the tightest of the
family's own component bounds, and needs the same `0 < zB.k` compactness does.
`reduce` keeps the first `o` components and forgets the rest. `split` cuts a bundle along a
column of `Λ` [Althoff-Krogh, Eq. 2], with the four direction heuristics `dirBox`, `dirPca`,
`dirFil` and `dirFlow`. `enclosingParallelotope` is the `Γ box(Γ⁻¹ Z_∩)` of that equation around
the whole bundle, which `shrink` (member by member) and `reduceCombined` (to one zonotope)
enclose by.
-/
