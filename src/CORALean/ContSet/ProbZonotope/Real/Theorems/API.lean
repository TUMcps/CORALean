import CORALean.ContSet.ProbZonotope.Real.Theorems.ConvMultivariateGaussian
import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian
import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq
import CORALean.ContSet.ProbZonotope.Real.Theorems.IntegrableExpNegNormSq
import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianEqWithDensity
import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEqWithDensity
import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawDensity
import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawPrintedPdfCounterexample
import CORALean.ContSet.ProbZonotope.Real.Theorems.OfGeneratorsLaws
import CORALean.ContSet.ProbZonotope.Real.Theorems.PlusLaws
import CORALean.ContSet.ProbZonotope.Real.Theorems.MtimesLaws
import CORALean.ContSet.ProbZonotope.Real.Theorems.MeanExact
import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianBox
import CORALean.ContSet.ProbZonotope.Real.Theorems.ConfidenceZonotopeProb
import CORALean.ContSet.ProbZonotope.Real.Theorems.ZonotopeProb
import CORALean.ContSet.ProbZonotope.Real.Theorems.UnsafeProbLe
import CORALean.ContSet.ProbZonotope.Real.Theorems.UnsafeProbPrintedCounterexample
import CORALean.ContSet.ProbZonotope.Real.Theorems.ProjectLaws
import CORALean.ContSet.ProbZonotope.Real.Theorems.VPolytopeExact
import CORALean.ContSet.ProbZonotope.Real.Theorems.RepresentsaEmptySetIff
import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfLeMaxIff
import CORALean.ContSet.ProbZonotope.Real.Theorems.GeneratorsMulTranspose
import CORALean.ContSet.ProbZonotope.Real.Theorems.ProbReduceEq
import CORALean.ContSet.ProbZonotope.Real.Theorems.ReduceGirardLawsOuter
import CORALean.ContSet.ProbZonotope.Real.Theorems.EncloseMeanOuter
import CORALean.ContSet.ProbZonotope.Real.Theorems.AbsLeCorner
import CORALean.ContSet.ProbZonotope.Real.Theorems.AbsNotMem
import CORALean.ContSet.ProbZonotope.Real.Theorems.IntervalProb
import CORALean.ContSet.ProbZonotope.Real.Theorems.UnitMeanIntervalCora
import CORALean.ContSet.ProbZonotope.Real.Theorems.IntervalCoraNotMem
import CORALean.ContSet.ProbZonotope.Real.Theorems.SupCoraLt
import CORALean.ContSet.ProbZonotope.Real.Theorems.SupIsLUB
import CORALean.ContSet.ProbZonotope.Real.Theorems.SqrtMulVecMemZonotope
import CORALean.ContSet.ProbZonotope.Real.Theorems.MemZonotopeOfQuadLt
import CORALean.ContSet.ProbZonotope.Real.Theorems.MaxAnti
import CORALean.ContSet.ProbZonotope.Real.Theorems.LeAddSumOfLevels
import CORALean.ContSet.ProbZonotope.Real.Theorems.PyramidOuter
import CORALean.ContSet.ProbZonotope.Real.Theorems.PyramidNotGeProb

/-!
# What a probabilistic zonotope guarantees, collected

A G-zonotope with certain mean is the Gaussian `N(c, G Gᵀ)`, with the density of
`GZonotopeLawDensity` when `G Gᵀ` is invertible; the operations map the laws exactly
(`PlusLaws`, `MtimesLaws`, `MeanExact`); the confidence sets carry the probability
`P[-m ≤ N(0, 1) ≤ m]ⁿ`, exactly or at least; and `UnsafeProbLe` bounds the probability of an
unsafe set by heights times volumes.
-/
