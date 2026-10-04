import CORALean.ContSet.ProbZonotope.Real.Operations.OfGenerators
import CORALean.ContSet.ProbZonotope.Real.Operations.Plus
import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ProbZonotope.Real.Operations.Mean
import CORALean.ContSet.ProbZonotope.Real.Operations.ConfidenceZonotope
import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
import CORALean.ContSet.ProbZonotope.Real.Operations.Project
import CORALean.ContSet.ProbZonotope.Real.Operations.VPolytope
import CORALean.ContSet.ProbZonotope.Real.Operations.RepresentsaEmptySet

/-!
# Probabilistic zonotope operations, collected

CORA's constructor from probabilistic generators (with its `sigma`), `plus`, `mtimes` by a
matrix, `mean`, and `zonotope`, the confidence set, built on the confidence set operator of a
zero-mean G-zonotope.
-/
