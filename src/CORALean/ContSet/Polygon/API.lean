import CORALean.ContSet.Polygon.Real.API
import CORALean.ContSet.Polygon.Float.API

/-!
# Polygons, both layers

CORA's `polygon` (`contSet/@polygon`): a possibly non-convex planar region, here a finite union
of convex polygons (`SetUnion (VPolytope (Vec ℝ 2))`), in `Real`, and in `Float` the same union
of float polytopes, each paying its own rounding into its error box.
-/
