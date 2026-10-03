import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
import CORALean.ContSet.Zonotope.Real.Operations.AutoTuneSetOrder
import CORALean.ContSet.Zonotope.Real.Operations.Bilin
import CORALean.ContSet.Zonotope.Real.Operations.Cube
import CORALean.ContSet.Zonotope.Real.Operations.Embed
import CORALean.ContSet.Zonotope.Real.Operations.EnclCoverLoop
import CORALean.ContSet.Zonotope.Real.Operations.EnclGenSel
import CORALean.ContSet.Zonotope.Real.Operations.EnclRatioLoop
import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
import CORALean.ContSet.Zonotope.Real.Operations.GenMap
import CORALean.ContSet.Zonotope.Real.Operations.GenSelection
import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Operations.LineClBasis
import CORALean.ContSet.Zonotope.Real.Operations.LineClKeep
import CORALean.ContSet.Zonotope.Real.Operations.LineClVolume
import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.MatMul
import CORALean.ContSet.Zonotope.Real.Operations.MatPow
import CORALean.ContSet.Zonotope.Real.Operations.MethCBasis
import CORALean.ContSet.Zonotope.Real.Operations.MethCFilter
import CORALean.ContSet.Zonotope.Real.Operations.MethCVolume
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffGenRec
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffOrEmpty
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.PCABasis
import CORALean.ContSet.Zonotope.Real.Operations.PCACovariance
import CORALean.ContSet.Zonotope.Real.Operations.PairDiff
import CORALean.ContSet.Zonotope.Real.Operations.PairSum
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Project
import CORALean.ContSet.Zonotope.Real.Operations.ProjectHighDim
import CORALean.ContSet.Zonotope.Real.Operations.QuadTaylor
import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach
import CORALean.ContSet.Zonotope.Real.Operations.RatioExceeds
import CORALean.ContSet.Zonotope.Real.Operations.Recentre
import CORALean.ContSet.Zonotope.Real.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxOrder
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBox
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByDropped
import CORALean.ContSet.Zonotope.Real.Operations.ReduceCoOptDir
import CORALean.ContSet.Zonotope.Real.Operations.ReduceCoOptSVD
import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Operations.ReduceHybridPC
import CORALean.ContSet.Zonotope.Real.Operations.ReduceLineCl
import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC
import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
import CORALean.ContSet.Zonotope.Real.Operations.Shift
import CORALean.ContSet.Zonotope.Real.Operations.Split
import CORALean.ContSet.Zonotope.Real.Operations.LongestGen
import CORALean.ContSet.Zonotope.Real.Operations.SplitLongestGen
import CORALean.ContSet.Zonotope.Real.Operations.SplitRank
import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
import CORALean.ContSet.Zonotope.Real.Operations.Rank
import CORALean.ContSet.Zonotope.Real.Operations.RotMat
import CORALean.ContSet.Zonotope.Real.Operations.Rotate
import CORALean.ContSet.Zonotope.Real.Operations.Underapproximate
import CORALean.ContSet.Zonotope.Real.Operations.UnderapproximateGen
import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Zonotope.Real.Operations.ExactPlus
import CORALean.ContSet.Zonotope.Real.Operations.NormUb
import CORALean.ContSet.Zonotope.Real.Operations.Radius2
import CORALean.ContSet.Zonotope.Real.Operations.GeneratorLength
import CORALean.ContSet.Zonotope.Real.Operations.ConstrSat
import CORALean.ContSet.Zonotope.Real.Operations.CartProd
import CORALean.ContSet.Zonotope.Real.Operations.SplitFirstGen

/-!
# What `Zonotope` computes

Only `reduce` bounds the generator count; the others grow it freely. `bilin` and `mtimesMatZonotope`
are a matrix zonotope acting on a set, at any bilinear map and at `Matrix.mulVecBilin` respectively;
`matMul` is the same at matrix multiplication, `matPow` iterates it and `quadTaylor` sums into
Prop. 3's Taylor term; `ofPoint`/`recentre` are a point and the origin-holding remainder.
`minkDiffAligned` is CORA's exact aligned-generator case of `minkDiff`, the only one not needing an
enclosure, and `minkDiffRep` is the general one, at a generator representation the caller offers and
this checks. `minkDiffOrEmpty` is that one again with the candidate chosen here rather than by the
caller, so that it is total — and wrapped, since the difference can be empty and no zonotope is.
`minkDiffGenRec` is Althoff's own recursion instead: exact, and `Set`-valued because nothing smaller
can be, the difference of two zonotopes not being one itself.

`girardSplit` is the ranking `reduceGirard` reduces by, named on its own because `reduceBox` reads
the same partition the other way round. `reduceByBox` computes nothing new — the diagonal block
`reduceBy` already builds, centred at the origin — and `reduceBox` is that at the partition
`reduce` actually picks, the origin where the order is already met. Together they name the error a
reduction pays, which is what an inner approximation subtracts back off.

`reduceByBasis` boxes along a basis, not the axes: `methCFilter`, `methCVolume` and `methCBasis`
pick `methC`'s, `pcaCovariance` and `pcaBasis` pick `pca`'s. `split` halves one generator into two
zonotopes that cover the original; `splitRank` picks which one. `supportBound` answers a direction
with no solver, the value attained; `shift` translates the centre alone — Prop. 6's `Z − vᵢ`.
-/
