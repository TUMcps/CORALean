module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Box
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirFil
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirFlow
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirPca
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirPcaCovariance
public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalAll
public import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalSupportFunc
public import CORALean.ContSet.ZonoBundle.Real.Operations.FacetLift
public import CORALean.ContSet.ZonoBundle.Real.Operations.FlowIndex
public import CORALean.ContSet.ZonoBundle.Real.Operations.GuardIntersect
public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
public import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
public import CORALean.ContSet.ZonoBundle.Real.Operations.Map
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
public import CORALean.ContSet.ZonoBundle.Real.Operations.Parallelotope
public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.ZonoBundle.Real.Operations.Pool
public import CORALean.ContSet.ZonoBundle.Real.Operations.Replace
public import CORALean.ContSet.ZonoBundle.Real.Operations.QuadMap
public import CORALean.ContSet.ZonoBundle.Real.Operations.Empty
public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.ContSet.ZonoBundle.Real.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Real.Operations.Shrink
public import CORALean.ContSet.ZonoBundle.Real.Operations.Split
public import CORALean.ContSet.ZonoBundle.Real.Operations.SupportBound
public import CORALean.ContSet.ZonoBundle.Real.Operations.Project
public import CORALean.ContSet.ZonoBundle.Real.Operations.CartProd
public import CORALean.ContSet.ZonoBundle.Real.Operations.Enlarge
public import CORALean.ContSet.ZonoBundle.Real.Operations.Isequal
public import CORALean.ContSet.ZonoBundle.Real.Operations.AllMembersFullDim
public import CORALean.ContSet.ZonoBundle.Real.Operations.IsCenter
public import CORALean.ContSet.ZonoBundle.Real.Operations.ContainsAll
public import CORALean.ContSet.ZonoBundle.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTight
public import CORALean.ContSet.ZonoBundle.Real.Operations.ConvHull
public import CORALean.ContSet.ZonoBundle.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightPoints
public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVertices
public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVerticesNonempty

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
enclose by. CORA's box `intervalAll` intersects the members' boxes; `intervalSupportFunc` is the
bounding box of the bundle itself, by its support function in `±eᵢ`.
-/
