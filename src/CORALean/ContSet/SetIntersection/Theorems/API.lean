module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.SetIntersection.Theorems.IntersectionExact
public import CORALean.ContSet.SetIntersection.Theorems.IsCompact
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseImageExact
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.SetIntersection.Theorems.MtimesOuter
public import CORALean.ContSet.SetIntersection.Theorems.PairwiseOuter
public import CORALean.ContSet.SetIntersection.Theorems.PlusOuter
public import CORALean.ContSet.SetIntersection.Theorems.ReduceOuter

/-!
# `SetIntersection`'s guarantees, collected

What holds of every intersection, once: membership and containment member by member
(`Basic`), convexity and compactness from the members', and the enclosures a bundle's
operations are instances of — `memberwise_outer` for an operation that maps or drops members,
`pairwise_outer` for one over every pair, `memberwise_image_exact` for a bijective image. The
operations' own guarantees are outer, as an intersection only shrinks under a branch-wise bound
(`⋂ M Sᵢ` covers `M (⋂ Sᵢ)`); the exact ones are `intersection_exact` and the bijective image.
-/
