module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.ConvMultivariateGaussian
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq
public import CORALean.ContSet.ProbZonotope.Real.Theorems.IntegrableExpNegNormSq
public import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianEqWithDensity
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEqWithDensity
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawDensity
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawPrintedPdfCounterexample
public import CORALean.ContSet.ProbZonotope.Real.Theorems.OfGeneratorsLaws
public import CORALean.ContSet.ProbZonotope.Real.Theorems.PlusLaws
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MtimesLaws
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MeanExact
public import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianBox
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ConfidenceZonotopeProb
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ZonotopeProb
public import CORALean.ContSet.ProbZonotope.Real.Theorems.UnsafeProbLe
public import CORALean.ContSet.ProbZonotope.Real.Theorems.UnsafeProbPrintedCounterexample
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ProjectLaws
public import CORALean.ContSet.ProbZonotope.Real.Theorems.Basic
public import CORALean.ContSet.ProbZonotope.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfLeMaxIff
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GeneratorsMulTranspose
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ProbReduceEq
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ReduceGirardLawsOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.EncloseMeanOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.AbsLeCorner
public import CORALean.ContSet.ProbZonotope.Real.Theorems.AbsNotMem
public import CORALean.ContSet.ProbZonotope.Real.Theorems.IntervalProb
public import CORALean.ContSet.ProbZonotope.Real.Theorems.UnitMeanIntervalCora
public import CORALean.ContSet.ProbZonotope.Real.Theorems.IntervalCoraNotMem
public import CORALean.ContSet.ProbZonotope.Real.Theorems.SupCoraLt
public import CORALean.ContSet.ProbZonotope.Real.Theorems.SupIsLUB
public import CORALean.ContSet.ProbZonotope.Real.Theorems.SqrtMulVecMemZonotope
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MemZonotopeOfQuadLt
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MaxAnti
public import CORALean.ContSet.ProbZonotope.Real.Theorems.LeAddSumOfLevels
public import CORALean.ContSet.ProbZonotope.Real.Theorems.PyramidOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.PyramidNotGeProb
public import CORALean.ContSet.ProbZonotope.Real.Theorems.EphMtimesExp
public import CORALean.ContSet.ProbZonotope.Real.Theorems.EphMtimesExpLeMax
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfExpMulVec

/-!
# What a probabilistic zonotope guarantees, collected

A G-zonotope with certain mean is the Gaussian `N(c, G Gᵀ)`, with the density of
`GZonotopeLawDensity` when `G Gᵀ` is invertible; the operations map the laws exactly
(`PlusLaws`, `MtimesLaws`, `MeanExact`); the confidence sets carry the probability
`P[-m ≤ N(0, 1) ≤ m]ⁿ`, exactly or at least; and `UnsafeProbLe` bounds the probability of an
unsafe set by heights times volumes.
-/
