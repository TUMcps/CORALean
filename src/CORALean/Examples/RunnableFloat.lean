import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContDynamics.LinParamSys.Operations.Canonical
import CORALean.ContSet.Zonotope.Float.Operations.CartProd
import CORALean.ContDynamics.LinearARX.Operations.InputMat
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRunFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachBoxFloatChecked
import CORALean.ContSet.ProbZonotope.Float.Operations.ProbReduce
import CORALean.ContSet.SpectraShadow.Float.Operations.ConvHull
import CORALean.ContSet.SpectraShadow.Float.Operations.Or
import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow
import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureExactFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalWFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpWFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHiFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLoFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinusFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.AffineDynamicsErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.AffineTimeIntervalOuterFloat
import CORALean.ContDynamics.LinearSys.Operations.AutoReachFloat
import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.ParticularSolutionTauErrorFloat
import CORALean.ContSet.Zonotope.Float.Operations.AutoTuneSetOrder
import CORALean.ContDynamics.LinearSys.Operations.BundleReachFloat
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachInputErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.OneStepFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachInnerRepFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.VarInputsFloat
import CORALean.ContSet.PolyZonotope.Float.Operations.ConvHull
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotopeFloat
import CORALean.ContDynamics.LinearSys.Operations.AffineTimePointNextFloat
import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptiveFloat
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.GirardReachFloat
import CORALean.ContDynamics.LinearSys.Operations.ManualReachFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepEpsFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderErrorFloat
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMuFloat
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachPolyFloat
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachPFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZonoFloat
import CORALean.ContSet.Zonotope.Float.Operations.OfIntervalMat
import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnionFloat
import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInputSplit
import CORALean.ContDynamics.LinParamSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepFloat
import CORALean.HybridDynamics.Operations.CheckFlowFloat
import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMapFloat
import CORALean.HybridDynamics.Operations.TimeIntervalStepSplitFloat
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachAlgFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.AdaptRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.CentreAbstrRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainderFloat
import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatFloat
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContSet.ConPolyZono.Float.Instances
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Conversion.Float.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Float.ConZonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.ConZonotope_to_VPolytope
import CORALean.ContSet.Conversion.Float.HPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid
import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.VPolytope_to_HPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope
import CORALean.ContSet.Ellipsoid.Float.Instances
import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir
import CORALean.ContSet.Ellipsoid.Float.Operations.Polygon
import CORALean.ContSet.Polygon.Float.Operations.Triangulation
import CORALean.ContSet.Polygon.Float.Operations.QuadMap
import CORALean.ContSet.Polygon.Float.Operations.QuadMapMixed
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.VPolytope.Float.Instances
import CORALean.ContSet.ZonoBundle.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.DominantDirections
import CORALean.ContSet.Zonotope.Float.Operations.EncloseMany
import CORALean.ContSet.Zonotope.Float.Operations.FilterOut
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffAligned
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRep
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretchInner
import CORALean.ContSet.Zonotope.Float.Operations.Minnorm
import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMatBox
import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.NN.Instances
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.ActivationLayerOf
import CORALean.NN.Layers.Operations.Pack
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Theorems.Basic
import CORALean.NN.Layers.Operations.SigmoidEnclosure
import CORALean.NN.Layers.Operations.SoftmaxBox
import CORALean.NN.NeuralNetwork
import CORALean.NN.Layers.Operations.FindRegionPolys
import CORALean.NN.Layers.Operations.PolyRelaxationPadTo
import CORALean.NN.Layers.Operations.RelaxationToPoly
import CORALean.NN.Operations.PropagateBounds
import CORALean.NN.Operations.Enclose
import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Theorems.HoldsOfCheck
import CORALean.Specification.Instances
import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLift
import CORALean.ContSet.Zonotope.Float.Operations.And
import CORALean.ContSet.Polygon.Float.Operations.And
import CORALean.ContSet.Polygon.Float.Operations.MinkDiff
import CORALean.ContSet.Polygon.Float.Operations.Subtract
import CORALean.ContSet.SetIntersection.Instances
import CORALean.ContSet.LevelSet.Float.Operations.ContainsPoint
import CORALean.ContSet.Taylm.Float.Operations.Times
import CORALean.ContSet.Taylm.Float.Operations.Basic
import CORALean.ContSet.Taylm.Float.Operations.Exp
import CORALean.ContSet.Conversion.Float.Interval_to_Taylm
import CORALean.ContSet.Equality.Float.Instances
import CORALean.ContSet.Equality.Float.Operations.Basic
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearARX.Operations.Feed
import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsPointApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsSetApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsPointSet
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApprox
import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
import CORALean.ContDynamics.LinearSys.Operations.Canonical
import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

/-!
# Every runnable algorithm, instantiated at a concrete float representation

Guarantees: every `def` below is a plain `def`, never `noncomputable def`, so
`lake build` fails the moment any of it stops computing — a generic `def` can
type-check and still fail once *instantiated*, since a structure *parameter*
is erased by the code generator but an ordinary function argument is not
(!216). A handful are also `#eval`'d, to show the definition runs to a value.

Not a guarantee: precision — `scripts/check-demo.sh` is what catches a silent
widening; an enclosure the size of the state space satisfies every theorem
here just as a tight one does.

Left out, and why: `LinearSys`'s float reaches are run in `RotationFloat`; its float sampling,
a location's stay, `LinParamSys`' step, a network in the loop and the nonlinear block are run
here, bar `varInputs` (`pending #1`), which has no float refinement yet;
`reachErrorFloat`/`reachInnerFloat` are real-valued guarantee objects, `spec:`;
`HPolytope.zonotope`/`vPolytopeBox`/`interval`/`conZonotope` and `verifyHalfspace`/
`verifyConvex` each ask for a `FloatBound`/`SupportBound` a solver alone can supply.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RunnableFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 24

/-- `m · 2 ^ e`. -/
def d {p : ℕ} (m e : ℤ) : Dyadic p := ⟨m, e⟩

/-- Zero width in every coordinate. -/
def zbox (n : ℕ) : Interval (Vec D n) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


/-! ## Every representation, built or converted to, at `D`

One small zonotope, two generators in two dimensions, and every other
representation reached from it by a `Float/` conversion — exercising the
conversion and supplying the rest of the section a value to run operations on. -/

def Z : Zonotope (Vec D 2) where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-2), d 0 0; d 0 0, d 1 (-2)]
  I_error := zbox 2

def I : Interval (Vec D 2) := Z.interval
def V : VPolytope (Vec D 2) := Z.vPolytope
def cZ : ConZonotope D (Vec D 2) := Z.conZonotope
def H : HPolytope D (Vec D 2) := Z.hPolytope (identityMat D 2)
def pZ : PolyZonotope (Vec D 2) := I.polyZonotope
def cpZ : ConPolyZono D (Vec D 2) := cZ.conPolyZono
def E : Ellipsoid D 2 := I.ellipsoid (d 1 0)
def zB : ZonoBundle (Vec D 2) := ⟨1, fun _ => Z⟩

-- more conversions, at the representations `Z`, `I`, `V`, `cZ` above already supply

def H_of_V : HPolytope D (Vec D 2) := V.hPolytope (identityMat D 2)
def H_of_cZ : HPolytope D (Vec D 2) := cZ.hPolytope (identityMat D 2)
def cZ_of_H : ConZonotope D (Vec D 2) := H.onCoefficients Z |>.conZonotopeOf Z
def V_of_cZ : VPolytope (Vec D 2) := cZ.vPolytopeBox
def cZ_of_V : ConZonotope D (Vec D 2) := V.conZonotope
def simplex2 : HPolytope D (Vec D 2) := VPolytope.simplex D 2


/-! ## A `LinearARX` and its companion matrix, at `D`

`toLinearSysDT` and `inputMat` only place entries, `0` and `1`, so they are exact at a rounded
scalar and their theorems are not restricted to ℝ (#117). -/

/-- `Ā = (1, -1)`, `B̄ = (1, 1, 0)`, as in `LinearARXReach`. -/
def arxD : LinearARX D 1 1 2 where
  Abar i := Matrix.of fun _ _ => if i.val = 0 then d 1 0 else d (-1) 0
  Bbar j := Matrix.of fun _ _ => if j.val = 2 then d 0 0 else d 1 0

def arxA : Mat D 2 2 := arxD.toLinearSysDT.A
def arxB : Mat D 2 1 := arxD.inputMat 0

#eval arxA 0 0
#eval arxA 0 1
#eval arxA 1 0
#eval arxA 1 1
#eval arxB 1 0

/-- Two scalar components `ẋ = x + u`, each input bound to the other's state: the merged flow is
`[[1, 1], [1, 1]]`, built with no rounding arithmetic, at `D` (#117). -/
def parP : ParallelHybridAutomaton ℐ𝒱[D] ℐ𝒱[D] 2
    (fun _ => Unit) D (fun _ => 1) 0 where
  comp _ := ⟨fun _ => ⟨zbox 1, LinearSys.canonicalFloat (fun _ _ => d 1 0), zbox 1, []⟩⟩
  binds i _ := .state i.rev 0

def parA : Mat D 2 2 := (parP.mergeFlows (fun _ => ())).A

#eval parA 0 0
#eval parA 0 1
#eval parA 1 0
#eval parA 1 1


/-! ## Every operation class each representation above instantiates -/

-- `Zonotope`: `Plus`, `LinComb`, `Reduce`, `Reindex`, `Mtimes`
def Z_plus : Zonotope (Vec D 2) := Z.plus Z
def Z_linComb : Zonotope (Vec D 2) := LinComb.linComb Z Z
def Z_reduce : Zonotope (Vec D 2) := Z.reduce 1
def Z_reindex : Zonotope (Vec D 2) :=
  Reindex.reindex (S := 𝒵[D]) (Equiv.refl (Fin 2)) Z
def Z_mtimes : Zonotope (Vec D 2) :=
  Mtimes.mtimes (S := 𝒵[D]) (identityMat D 2) Z

-- `SetUnion` of float zonotopes: `Plus`, `Reduce`, `Mtimes`, generic over the member type
def uZ : SetUnion (Zonotope (Vec D 2)) := ⟨[Z, Z_mtimes]⟩
def uZ_plus : SetUnion (Zonotope (Vec D 2)) := Plus.plus uZ uZ
def uZ_reduce : SetUnion (Zonotope (Vec D 2)) := Reduce.reduce uZ 1
def uZ_mtimes : SetUnion (Zonotope (Vec D 2)) :=
  Mtimes.mtimes (S := fun n => SetUnion (Zonotope (Vec D n))) (identityMat D 2) uZ

-- `Interval`: `Plus`, `MinkDiff`, `Intersection`, `LinComb`, `Reduce`, `Reindex`, `Mtimes`
def I_plus : Interval (Vec D 2) := Plus.plus I I
def I_minkDiff : Interval (Vec D 2) := MinkDiff.minkDiff I I
def I_intersection : Interval (Vec D 2) := Intersection.intersection I I
def I_linComb : Interval (Vec D 2) := LinComb.linComb I I
def I_reduce : Interval (Vec D 2) := Reduce.reduce I 1
def I_reindex : Interval (Vec D 2) :=
  Reindex.reindex (S := ℐ𝒱[D]) (Equiv.refl (Fin 2)) I
def I_mtimes : Interval (Vec D 2) :=
  Mtimes.mtimes (S := ℐ𝒱[D]) (identityMat D 2) I


/-! ## The float interval-matrix chain: `matMul`/`matPow`/`smul`/`expIntervalEnclosure`

A point interval matrix, its float `expIntervalEnclosure`, and an interval
matrix times a box through the interval-matrix `Mtimes` instance (#1, phase 2). -/

def matExpA : Interval (Mat D 2 2) :=
  ⟨!![d 0 0, d 1 (-1); d (-1) (-1), d 0 0], !![d 0 0, d 1 (-1); d (-1) (-1), d 0 0]⟩

def expEnclosureRun : Interval (Mat D 2 2) := MatExp.expIntervalEnclosure matExpA 4

-- the exact second-order interval exponential, at t = 1/2 (#1)
def expWRun : Interval (Mat D 2 2) := MatExp.expW matExpA.inf (d 1 (-1))

def expIntervalWRun : Interval (Mat D 2 2) := MatExp.expIntervalW matExpA (d 1 (-1))

def expEnclosureExactRun : Interval (Mat D 2 2) :=
  MatExp.expIntervalEnclosureExact matExpA (d 1 (-1)) 4

-- the diagonal factor γ(a) = a t + ½ a² t² at a = 1, and its bounds over [-3, 1]
def quadTermRun : Interval D := MatExp.quadTerm (d 1 (-1)) (d 1 0)

def quadTermBoundsRun : Interval D :=
  ⟨MatExp.quadTermLo (d 1 (-1)) (d (-3) 0) (d 1 0), MatExp.quadTermHi (d 1 (-1)) (d (-3) 0) (d 1 0)⟩

def mtimesIntervalMatRun : Interval (Vec D 2) :=
  Mtimes.mtimes (𝕄 := ℐ[D]) (S := ℐ𝒱[D])
    matExpA I

-- the same interval matrix, at `expEnclosureRun`, times a float zonotope (#1, phase 3 prep)
def mtimesIntervalMatZonoRun : Zonotope (Vec D 2) :=
  Mtimes.mtimes (𝕄 := ℐ[D]) (S := 𝒵[D])
    expEnclosureRun Z

-- `HPolytope`: `Reduce`, `Intersection`
def H_reduce : HPolytope D (Vec D 2) := Reduce.reduce H 1
def H_intersection : HPolytope D (Vec D 2) := Intersection.intersection H H

-- `VPolytope`: `Plus`, `Intersection`, `LinComb`, `Reduce`, `Mtimes`
def V_plus : VPolytope (Vec D 2) := Plus.plus V V
def V_intersection : VPolytope (Vec D 2) := Intersection.intersection V V
def V_linComb : VPolytope (Vec D 2) := LinComb.linComb V V
def V_reduce : VPolytope (Vec D 2) := Reduce.reduce V 1
def V_mtimes : VPolytope (Vec D 2) :=
  Mtimes.mtimes (S := 𝒱𝒫[D]) (identityMat D 2) V

-- `ConZonotope`: `Plus`, `LinComb`, `Reduce`
def cZ_plus : ConZonotope D (Vec D 2) := Plus.plus cZ cZ
def cZ_linComb : ConZonotope D (Vec D 2) := LinComb.linComb cZ cZ
def cZ_reduce : ConZonotope D (Vec D 2) := Reduce.reduce cZ 1

-- `PolyZonotope`: `Plus`, `LinComb`, `Reduce`, `Mtimes`
def pZ_plus : PolyZonotope (Vec D 2) := Plus.plus pZ pZ
def pZ_linComb : PolyZonotope (Vec D 2) := LinComb.linComb pZ pZ
def pZ_reduce : PolyZonotope (Vec D 2) := Reduce.reduce pZ 1
def pZ_mtimes : PolyZonotope (Vec D 2) :=
  Mtimes.mtimes (S := 𝒫𝒵[D]) (identityMat D 2) pZ
def pZ_convHull : PolyZonotope (Vec D 2) := PolyZonotope.convHull pZ pZ

-- the quadratic map `x ↦ xᵀ x` of `pZ`, its two-operand pairings, and the varying input part
def pZ_quadMap : PolyZonotope (Vec D 2) := PolyZonotope.quadMap
    (fun _ : Fin 2 => identityMat D 2) pZ
def pZ_bilin : PolyZonotope (Vec D 2) :=
  PolyZonotope.bilin (fun _ : Fin 2 => identityMat D 2) pZ.dependent pZ.dependent rfl
def pZ_quadMapMixed : PolyZonotope (Vec D 2) :=
  PolyZonotope.quadMapMixed (fun _ : Fin 2 => identityMat D 2) pZ pZ
def pZ_varInputs : PolyZonotope (Vec D 2) :=
  varInputsFloat (identityMat D 2) (fun _ : Fin 2 => identityMat D 2) pZ pZ pZ

-- `ConPolyZono`: `Plus`, `Reduce`, `Intersection`, `Mtimes`
def cpZ_plus : ConPolyZono D (Vec D 2) := Plus.plus cpZ cpZ
def cpZ_reduce : ConPolyZono D (Vec D 2) := Reduce.reduce cpZ 1
def cpZ_intersection : ConPolyZono D (Vec D 2) := Intersection.intersection cpZ cpZ
def cpZ_mtimes : ConPolyZono D (Vec D 2) :=
  Mtimes.mtimes (S := fun k => ConPolyZono D (Vec D k)) (identityMat D 2) cpZ

-- `ZonoBundle`: `Plus`, `LinComb`, `Intersection`, `Reduce`, `Reindex`, `Mtimes`
def zB_plus : ZonoBundle (Vec D 2) := Plus.plus zB zB
def zB_linComb : ZonoBundle (Vec D 2) := LinComb.linComb zB zB
def zB_intersection : ZonoBundle (Vec D 2) := Intersection.intersection zB zB
def zB_reduce : ZonoBundle (Vec D 2) := Reduce.reduce zB 1
def zB_reindex : ZonoBundle (Vec D 2) :=
  Reindex.reindex (S := 𝒵ℬ[D]) (Equiv.refl (Fin 2)) zB
def zB_mtimes : ZonoBundle (Vec D 2) :=
  Mtimes.mtimes (S := 𝒵ℬ[D]) (identityMat D 2) zB

-- `Ellipsoid`: `Mtimes` alone — the rest of its operations have no float file yet
def E_mtimes : Ellipsoid D 2 := Mtimes.mtimes (identityMat D 2) E

-- `ProbZonotope`: the mean zonotope `Z` and the identity covariance, then `probReduce`
def probZ : ProbZonotope D 2 := ⟨Z, Interval.point !![d 1 0, d 0 0; d 0 0, d 1 0]⟩
def probZ_probReduce : ProbZonotope D 2 := probZ.probReduce

-- `SpectraShadow`: the shadow of `Z`, and its convex hull with the shadow of `Z + Z`
def spS : SpectraShadow D (Vec D 2) := Z.spectraShadow
def spS_convHull : SpectraShadow D (Vec D 2) := spS.convHull_ Z_plus.spectraShadow
def spS_or : SpectraShadow D (Vec D 2) := spS.or Z_plus.spectraShadow


/-! ## The matrices a continuous-time step multiplies by (#1, phase 3)

`A = [-1 -4; 4 -1]` over a step `r = 2⁻⁵`: the order the float remainder admits,
then `F`, the input term of order `1` and the input remainder at order `4`. -/

def stepA : Interval (Mat D 2 2) := Interval.point !![d (-1) 0, d (-4) 0; d 4 0, d (-1) 0]
def stepR : D := d 1 (-5)

def stepOrderRun : Option ℕ :=
  MatExp.admissibleOrder (MatExp.normUpperBound (Interval.smul stepR stepR stepA)) 2 20
def correctionRun : Interval (Mat D 2 2) := MatExp.intervalCorrectionMatrix stepA stepR 4
def inputTermRun : Interval (Mat D 2 2) := MatExp.intervalInputTerm stepA stepR 1
def inputRemainderRun : Interval (Mat D 2 2) := MatExp.intervalInputRemainder stepA stepR 4


/-! ## A continuous-time system sampled in floats (#1)

The same `A` and `r`, sampled by `discretizeEnclosureFloat` into a `LinParamSysDT` over float
interval matrices, and five steps of its `reach` under the input set `Z`. -/

def ctSys : LinearSys D 2 := LinearSys.canonical (!![d (-1) 0, d (-4) 0; d 4 0, d (-1) 0])
def ctSysD : LinParamSysDT ℐ[D] 2 :=
  ctSys.discretizeEnclosureFloat stepR 4
def ctReachRun : Zonotope (Vec D 2) := ctSysD.reach (S := 𝒵[D])
    ⟨Z, Z, 0, 5⟩ ⟨2, two_pos⟩

-- what the input enclosures of five sampled steps owe, and the box one step pays (#1)
def ctErrorBoxRun : Zonotope (Vec D 2) := ctSys.timePointStepErrorBoxFloat stepR 4 Z
def ctInputErrorRun : Zonotope (Vec D 2) := ctSys.reachInputErrorFloat stepR 4 Z 5

-- CORA's `oneStep` from `Z`: `Z` re-centred as the inputs `U`, `Z`'s centre as the constant `u`
def oneStepTpRun : Zonotope (Vec D 2) := (ctSys.oneStepFloat Z (Recentre.recentre Z) Z.c stepR 4).1
def oneStepTiRun : Zonotope (Vec D 2) := (ctSys.oneStepFloat Z (Recentre.recentre Z) Z.c stepR 4).2

/-- The float Minkowski difference at a checked representation: the box `[-2, 2]²` minus a box of
half-width `½` at `x₀ = ⅛`, its generators written in the minuend's by `M = ¼ I`, certified with
the right inverse `H = ½ I` and the margin shrunk by `15/16`. -/
def minkDiffMinuend : Zonotope (Vec D 2) where
  h := 2
  c := ![d 0 0, d 0 0]
  G := !![d 1 1, d 0 0; d 0 0, d 1 1]
  I_error := zbox 2
def minkDiffSubtrahend : Zonotope (Vec D 2) where
  h := 2
  c := ![d 1 (-3), d 0 0]
  G := !![d 1 (-1), d 0 0; d 0 0, d 1 (-1)]
  I_error := zbox 2
def minkDiffOpt : Option (Zonotope (Vec D 2)) :=
  minkDiffMinuend.minkDiffRep minkDiffSubtrahend (fun i j => if i = j then d 1 (-2) else d 0 0)
    (d 15 (-4)) !![d 1 (-1), d 0 0; d 0 0, d 1 (-1)]
def minkDiffRun : Zonotope (Vec D 2) := minkDiffOpt.getD (Zonotope.point ![d 0 0, d 0 0])

/-- The non-square Minkowski difference pinning the generator orientation, explained in
`minkDiffRepCandidate`'s module docstring. -/
def minkDiffNSMinuend : Zonotope (Vec D 2) where
  h := 3
  c := ![d 0 0, d 0 0]
  G := !![d 1 0, d 0 0; d 0 0, d 1 0; d 1 0, d 1 0]
  I_error := zbox 2
def minkDiffNSSubtrahend : Zonotope (Vec D 2) where
  h := 2
  c := ![d 0 0, d 0 0]
  G := !![d 1 (-1), d 0 0; d 1 (-2), d 1 (-1)]
  I_error := zbox 2
def minkDiffNSOpt : Option (Zonotope (Vec D 2)) :=
  let M : Mat D 3 2 := !![d 1 (-1), d 0 0; d 0 0, d 1 (-2); d 0 0, d 1 (-2)]
  minkDiffNSMinuend.minkDiffRep minkDiffNSSubtrahend (fun i j => M i j) (d 1 (-1))
    !![d 3 (-2), d (-3) (-3); d (-1) (-2), d 5 (-3); d 1 (-2), d 3 (-3)]
def minkDiffNSRun : Zonotope (Vec D 2) := minkDiffNSOpt.getD (Zonotope.point ![d 0 0, d 0 0])

/-- The aligned difference of `minkDiff*`'s operands (subtrahend `¼` of the minuend), shrunk by
`ρ = 15/16`: at `ρ = 1` it is exact and leaves the check no slack. The stretch at `μ = ¾` is that
exact difference rounded outward; at `μ = ⅝` it is certified inner by the same check. -/
def minkDiffAlignedOpt : Option (Zonotope (Vec D 2)) :=
  minkDiffMinuend.minkDiffAligned minkDiffSubtrahend rfl (d 15 (-4))
    !![d 1 (-1), d 0 0; d 0 0, d 1 (-1)]
def minkDiffAlignedRun : Zonotope (Vec D 2) := minkDiffAlignedOpt.getD
    (Zonotope.point ![d 0 0, d 0 0])
def minkDiffStretchRun : Zonotope (Vec D 2) :=
  minkDiffMinuend.minkDiffStretch minkDiffSubtrahend fun _ => d 3 (-2)
def minkDiffStretchInnerOpt : Option (Zonotope (Vec D 2)) :=
  minkDiffMinuend.minkDiffStretchInner minkDiffSubtrahend (fun _ => d 5 (-3))
    !![d 1 (-1), d 0 0; d 0 0, d 1 (-1)]
def minkDiffStretchInnerRun : Zonotope (Vec D 2) :=
  minkDiffStretchInnerOpt.getD (Zonotope.point ![d 0 0, d 0 0])

/-- A location flowing by the same `A`, its input `Z` off the origin, and its stay over
`[0, r]` from `Z` by the float step and by the split float step. -/
def ctLoc : Location 𝒵[D] 𝒵[D] Unit D 2 :=
    ⟨Z, ctSys, Z, []⟩
def locStepRun : Zonotope (Vec D 2) := ctLoc.timeIntervalStepFloat stepR 4 Z
def locSplitRun : Zonotope (Vec D 2) := ctLoc.timeIntervalStepSplitFloat stepR 4 Z

/-- The guard hyperplane `x₁ = 9/8` of unit normal `e₁`: the cut of `Z` along `e₂` and the
Girard and Le Guernic bundle over the identity basis, and the reach sets of `ctLoc` that
`checkFlowFloat` keeps (the flow at the plane has an outward component). -/
def hpNormal : Vec D 2 := ![d 1 0, d 0 0]
def hpOffset : D := d 9 (-3)
def hpBasis : Mat D 2 2 := !![d 1 0, d 0 0; d 0 0, d 1 0]
def zonoGirardUpperRun : D := Location.zonoGirardUpperFloat Z hpNormal hpOffset ![d 0 0, d 1 0]
def zonoGirardRun : ZonoBundle (Vec D 2) :=
  Location.guardIntersectZonoGirardFloat [hpBasis] Z [] hpNormal hpOffset
def checkFlowRun : List (Zonotope (Vec D 2)) := ctLoc.checkFlowFloat hpNormal hpOffset [Z]

/-- A location drifting along `e₁` at unit speed under a slow rotation, and the guard map of the
box of half-width `2⁻⁴` about `(1, 0)` onto `x₁ = 1`, `tmax = 2⁻³`, two Taylor terms. -/
def hpMapLoc : Location 𝒵[D] 𝒵[D] Unit D 2 :=
  ⟨Z, LinearSys.canonicalFloat !![d 0 0, d (-1) (-1); d 1 (-1), d 0 0], Zonotope.point
      ![d 1 0, d 0 0], []⟩
def hpMapR0 : Zonotope (Vec D 2) where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-4), d 0 0; d 0 0, d 1 (-4)]
  I_error := zbox 2
def hpMapRun : Option (Zonotope (Vec D 2)) :=
  hpMapLoc.guardIntersectHyperplaneMapFloat hpNormal (d 1 0) hpMapR0 (d 1 (-3)) 2 10 10 20

/-- `A` known only to `±2⁻⁵` entrywise, as a `LinParamSys` over float interval matrices: an
admissible order, one step of its flow, its input solution over `Z`, and five sampled steps. -/
def lpA : Interval (Mat D 2 2) :=
  ⟨!![d (-33) (-5), d (-129) (-5); d 127 (-5), d (-33) (-5)],
    !![d (-31) (-5), d (-127) (-5); d 129 (-5), d (-31) (-5)]⟩
def lpSys : LinParamSys ℐ[D] 2 := LinParamSys.canonical lpA
def lpOrderRun : Option ℕ := lpSys.reachOrderFloat stepR stepR 2
def lpStepRun : Zonotope (Vec D 2) := lpSys.timeIntervalStepFloat stepR 4 Z
def lpInputRun : Zonotope (Vec D 2) := lpSys.inputSolutionFloat stepR 4 Z
def lpReachRun : Zonotope (Vec D 2) :=
  (lpSys.discretizeEnclosureFloat stepR 4).reach (S := 𝒵[D])
    ⟨Z, lpInputRun, 0, 5⟩
    ⟨2, two_pos⟩
/-- Four windows of `[0, 2⁻³]` at every member, each from the first by scaling and squaring. -/
def lpWindowsRun : Option (List (Zonotope (Vec D 2))) := lpSys.reachFloat
    ⟨Z, 0, 1 / 8⟩ ⟨stepR, 4, 2⟩

/-- The same four windows with an input: `Z` re-centred at the origin, whose contribution
`P^R(t_{k+1})` accumulates by `particularSolutionFloat`; then `Z` itself, split at its centre,
the constant half carried across windows by `constPropagateFloat`. -/
def lpInputSet : Zonotope (Vec D 2) := Recentre.recentre Z
def lpParticularRun : Option (Zonotope (Vec D 2)) := lpSys.particularSolutionFloat stepR 4
    2 lpInputSet 2
def lpConstRun : Zonotope (Vec D 2) := lpSys.constPropagateFloat stepR 4 2 (Z.c) 3
def lpInputWindowsRun : Option (List (Zonotope (Vec D 2))) :=
  lpSys.reachFloatInput lpInputSet ⟨Z, 0, 1 / 8⟩ ⟨stepR, 4, 2⟩
def lpSplitWindowsRun : Option (List (Zonotope (Vec D 2))) :=
  lpSys.reachFloatInputSplit Z ⟨Z, 0, 1 / 8⟩ ⟨stepR, 4, 2⟩


/-! ## The continuous-time inner approximation in floats (#129)

`ẋ = -x + u` from `[1, 2]` under `|u| ≤ 2⁻⁶`: one step of `r = ⅛`, and five sampled steps at
order `2`. Each is a float outer set, its budget, and their certified difference, `M` writing
every budget generator in the outer set's first and `H` the least-squares right inverse
`gᵀ/‖g‖²`, the margin shrunk by `15/16`. -/

def ctInnerSys : LinearSys D 1 := LinearSys.canonical (!![d (-1) 0])
def ctInnerX : Zonotope (Vec D 1) := ⟨1, ![d 3 (-1)], !![d 1 (-1)], zbox 1⟩
def ctInnerU : Zonotope (Vec D 1) := ⟨1, ![d 0 0], !![d 1 (-6)], zbox 1⟩
-- one step: the float step, its budget, and the step minus its budget
def ctInnerStep : Zonotope (Vec D 1) :=
  ctInnerSys.timePointStepInputFloat (d 1 (-3)) 4 ctInnerX ctInnerU
def ctInnerStepError : Zonotope (Vec D 1) :=
  ctInnerSys.timePointStepInnerErrorFloat (d 1 (-3)) 4 ctInnerX ctInnerU
def ctInnerStepOpt : Option (Zonotope (Vec D 1)) :=
  let S := ctInnerSys.timePointStepInputFloat (d 1 (-3)) 4 ctInnerX ctInnerU
  let B := ctInnerSys.timePointStepInnerErrorFloat (d 1 (-3)) 4 ctInnerX ctInnerU
  ctInnerSys.timePointStepInnerRepFloat (d 1 (-3)) 4 ctInnerX ctInnerU
    (fun i j => if i.val = 0 then divUp (absolute (B.G j 0)) (absolute (S.G i 0)) else d 0 0)
    (d 15 (-4)) (fun i _ => divDown (S.G i 0) (sumUp fun k => mulUp (S.G k 0) (S.G k 0)))
def ctInnerStepRun : Zonotope (Vec D 1) := ctInnerStepOpt.getD (Zonotope.point ![d 0 0])
-- five sampled steps: the float run, its budget, and the run minus its budget
def ctInnerReach : Zonotope (Vec D 1) :=
  (ctInnerSys.discretizeEnclosureFloat (d 1 (-3)) 4).reach (S := 𝒵[D])
    ⟨ctInnerX, ctInnerSys.inputSolutionFloat (d 1 (-3)) 4 ctInnerU, 0, 5⟩ ⟨2, two_pos⟩
def ctInnerReachError : Zonotope (Vec D 1) :=
  ctInnerSys.reachErrorFloat (d 1 (-3)) 4 2 two_pos ctInnerX ctInnerU 5
def ctInnerReachOpt : Option (Zonotope (Vec D 1)) :=
  let R := (ctInnerSys.discretizeEnclosureFloat (d 1 (-3)) 4).reach
    (S := 𝒵[D])
    ⟨ctInnerX, ctInnerSys.inputSolutionFloat (d 1 (-3)) 4 ctInnerU, 0, 5⟩ ⟨2, two_pos⟩
  let B := ctInnerSys.reachErrorFloat (d 1 (-3)) 4 2 two_pos ctInnerX ctInnerU 5
  ctInnerSys.reachInnerRepFloat (d 1 (-3)) 4 2 two_pos ctInnerX ctInnerU 5
    (fun i j => if i.val = 0 then divUp (absolute (B.G j 0)) (absolute (R.G i 0)) else d 0 0)
    (d 15 (-4)) (fun i _ => divDown (R.G i 0) (sumUp fun k => mulUp (R.G k 0) (R.G k 0)))
def ctInnerReachRun : Zonotope (Vec D 1) := ctInnerReachOpt.getD (Zonotope.point ![d 0 0])


/-! ## Matrix zonotopes in floats (#1)

`lpA` as a float matrix zonotope, one generator per entry, scaled by `r` and enclosed by its
exponential at order `3`; `ctSys` sampled through a matrix zonotope and five steps of its
`reach`; and the matrix-zonotope input solution of `lpA` over `Z`. -/

def mzA : Zonotope (Mat D 2 2) := Zonotope.ofIntervalMat lpA
def mzExpRun : Zonotope (Mat D 2 2) :=
  MatExp.expMatZonoEnclosure (Zonotope.matSmul stepR stepR mzA) 3
-- the system matrix itself sampled through a point matrix zonotope, and its reach
def ctSysMZ : LinParamSysDT 𝕄𝒵[D] 2 :=
  ctSys.discretizeMatZonotopeFloat stepR 4
def ctMZReachRun : Zonotope (Vec D 2) := ctSysMZ.reach (S := 𝒵[D])
    ⟨Z, Z, 0, 5⟩ ⟨2, two_pos⟩
def lpMZSys : LinParamSys 𝕄𝒵[D] 2 := LinParamSys.canonical mzA
def lpMZInputRun : Zonotope (Vec D 2) := lpMZSys.inputSolutionZonoFloat stepR 4 Z


/-! ## The fully-automated scheme's `Alg. 1` and the step error estimates, in floats (#1)

`ctSys` under the input `Z`, entered through the identity: four windows of `[0, 2⁻³]` at the
fixed step `r`, order `4` and zonotope order `2`; the four `ℝ`-valued estimates the adaptive
schemes tune against, rounded up at `r`, order `4` and `Z`; a step whose order is searched
for against an admissible remainder; Girard's scheme over `[0, 2⁻³]` at inputs of norm at
most `2⁻⁴`; CORA's `errorSolution_adaptive` with its order, `Z` dynamic and static; and the
input solution's orders `1 … 4` and `H(t_{k+1})` from `Z`, under the constant `Z`'s centre. -/

def manualReachRun : Option (List (Zonotope (Vec D 2))) :=
  ctSys.manualReachFloat (identityMat D 2) { X₀ := Z, U := Z, tFinal := 1 / 8 } ⟨stepR, 4, 2⟩
def curvatureErrorRun : D := ctSys.timeIntervalStepCurvatureErrorFloat stepR 4 Z
def intervalErrorRun : D := ctSys.timeIntervalStepErrorFloat stepR 4 Z
def pointErrorRun : D := ctSys.timePointStepErrorFloat stepR 4 Z
def remainderErrorRun : D := ctSys.timePointStepRemainderErrorFloat stepR 4 Z
/-- One step from `Z` at the first order whose remainder bound is under `2⁻²⁰`. -/
def stepEpsRun : Option (Zonotope (Vec D 2)) := ctSys.timeIntervalStepEpsFloat stepR
    (d 1 (-20)) 20 Z
def girardRun : Option (List (Zonotope (Vec D 2))) := ctSys.girardReachFloat Z
    (d 1 (-4)) stepR (1 / 8)
def errorSolutionRun : Zonotope (Vec D 2) := ctSys.errorSolutionAdaptiveFloat stepR 4 Z (some Z)
def errorOrderRun : Option ℕ := ctSys.errorSolutionOrderFloat (d 1 (-4)) stepR Z 20
def inputTailRun : Zonotope (Vec D 2) := ctSys.inputTaylorSumTailFloat stepR Z 4
def timePointNextRun : Zonotope (Vec D 2) := ctSys.affineTimePointNextFloat Z Z.c stepR 4


/-! ## The fully-automated scheme's `Alg. 2`, its curvature enclosure and its tuning, in floats (#1)

`ctSys` under the input `Z` and horizon `2⁻³`: the curvature enclosure of eq. (15)-(16) with its
integrated correction `G`, and eq. (22)'s set, at `r` and order `4` from `Z` and the constant
`Z`'s centre; the Euclidean radius of `Z`'s box; the three tuning quantities, at `[e^{A r}]`
for `e^{A t_k}`; the zonotope order, the step size and order searched for, one iteration and
the whole loop. -/

def constCorrectionRun : Interval (Mat D 2 2) :=
  MatExp.intervalConstCorrectionMatrix (Interval.point ctSys.A) stepR 4
def curvatureRun : Zonotope (Vec D 2) := MatExp.curvatureEnclosure
    (Interval.point ctSys.A) Z Z.c stepR 4
def timeIntervalOuterRun : Zonotope (Vec D 2) := ctSys.affineTimeIntervalOuterFloat Z Z.c stepR 4
def errUpRun : D := Z.errUp
/-- `‖G^{(-)}_h‖₂` of `Z`'s generators at `[e^{A r}]`, from above. -/
def genMinusRun : D := genOpNormUp 64 (MatExp.genMinus (ctSys.expIntervalFloat stepR stepR 4) Z)
def affineErrorRun : D := ctSys.affineDynamicsErrorFloat Z Z.c stepR 4
def particularErrorRun : D :=
  ctSys.particularSolutionErrorFloat (ctSys.expIntervalFloat stepR stepR 4) Z stepR 4
def particularTauErrorRun : D :=
  ctSys.particularSolutionTauErrorFloat (ctSys.expIntervalFloat stepR stepR 4) Z stepR 4
/-- The zonotope order that clears a share of `1/100`. -/
def setOrderRun : Option ℕ := Zonotope.autoTuneSetOrder Z (1 / 100) 0 (Z.h + 1)
/-- Lines 5-15 from `t_k = 0` at `Δt_{k-1} = 2⁻³`, `ε_max = 1`, `ζ = 1/2`. -/
def autoTuneRun : Option (D × ℕ) :=
  ctSys.autoTuneDeltaTFloat (ctSys.expIntervalFloat zero zero 4) Z Z.c 0 (1 / 8) 1 (1 / 2) 0
    (d 1 (-3)) 20 30 Z
/-- One iteration of `Alg. 2` from `Z` under the input `Z`, horizon `2⁻³`. -/
def autoStepRun : Option (LinearSys.AutoStateFloat D 2 × Zonotope (Vec D 2)) :=
  ctSys.autoStepFloat Z Z (d 1 (-3)) 1 (1 / 2) 20 30 (LinearSys.autoInitFloat Z (d 1 (-3)))
def autoReachRun : Option (List (ℚ × ℚ × Zonotope (Vec D 2))) :=
  ctSys.autoReachFloat Z Z (d 1 (-3)) 1 (1 / 2) 20 30 10

/-! ## Zonotope bundles and backward reachability in floats (#1)

`ctSys` once more. `bundleReachFloat` propagates a one-member bundle and `Z` through three steps
of `[e^{Ar}]` at order `4`. The minimal backward reachable set's algorithm runs from the
state before the first iteration, through one step and two, with `cZ` as the target set, `Z` for
both input sets and a constant `Z` as the centre trajectory's contribution; its support value
and `p` are read in the direction of the first coordinate, `N = I`. The Taylor order is `4`
and the matrix exponentials are squared twice. -/

def bundleRun : List (ZonoBundle (Vec D 2)) := ctSys.bundleReachFloat zB Z stepR 4 3
def minBackInitRun : LinearSys.MinBackReachStateOf D (Zonotope (Vec D 2))
    (ConZonotope D (Vec D 2)) :=
  ctSys.minBackReachInitFloat Z Z (d 0 0) 4
def minBackStepRun : LinearSys.MinBackReachStateOf D (Zonotope (Vec D 2))
    (ConZonotope D (Vec D 2)) :=
  ctSys.minBackReachStepFloat cZ Z Z (fun _ => Z) stepR 4 2 minBackInitRun
def minBackRunRun : LinearSys.MinBackReachStateOf D (Zonotope (Vec D 2))
    (ConZonotope D (Vec D 2)) :=
  ctSys.minBackReachRunFloat cZ Z Z (fun _ => Z) (d 0 0) stepR 4 2 2
def minBackSupportRun : D :=
  ctSys.minBackReachSupportFloat cZ Z Z (fun _ => Z) (identityMat D 2) (d 0 0) stepR 4 2 2 0
def minBackPRun : Fin 2 → D :=
  ctSys.minBackReachPFloat cZ Z Z (fun _ => Z) (identityMat D 2) (d 0 0) stepR 4 2 2
/-- The maximal set's curvature radius for `Z` as `box(X_end)`, and the target polytope `H` eroded
by `Z` as `F box(X_end)` and by the ball of that radius. -/
def maxBackMuRun : D := ctSys.maxBackReachMuFloat stepR 4 4 Z
def maxBackPolyRun : HPolytope D (Vec D 2) := LinearSys.maxBackReachPolyFloat 4 H Z maxBackMuRun


/-! ## The four Box operations `LinearSysDT.reachErrorFloat` sums

Each used to return a `Real.Zonotope`, read back through `toReal`, and so was
`noncomputable`; each now computes in `D` directly. -/

def plusBoxRun : Interval (Vec D 2) := Zonotope.plusBox Z Z
def mtimesBoxRun : Interval (Vec D 2) := Zonotope.mtimesBox (identityMat D 2) Z
def reduceByBoxRun : Zonotope (Vec D 2) :=
  Z.reduceByBox (Partition.split 2 0 : Split (Fin Z.h) into (Fin 2) ⊕ (Fin 0))
def reduceGirardBoxRun : Zonotope (Vec D 2) := Zonotope.reduceGirardBox Z 1
-- what `[e^{AΔt}] Z` holds beyond `A Z` for every `A` in the interval matrix (#129)
def mtimesIntervalMatBoxRun : Interval (Vec D 2) :=
  Zonotope.mtimesIntervalMatBox expEnclosureRun Z


/-! ## The zonotope operations that pick, delete, measure and orient

`dominantDirections` (the two generators of `Z`, if their parallelotope ranks first), `filterOut`
of `Z` and a larger cell holding it (the small one is deleted), `minnorm` (an upper bound on the
radius of the ball around the centre, `1/4` for `Z`) and `encloseMany` along the diagonal. -/

/-- A cell holding `Z`: the same centre, generators four times as long. -/
def Zbig : Zonotope (Vec D 2) where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 0, d 0 0; d 0 0, d 1 0]
  I_error := zbox 2

def dominantDirectionsRun : Option (Mat D 2 2) := Z.dominantDirections
def filterOutRun : List (Fin 2) :=
  (List.finRange 2).filter fun i => decide (i ∈ Zonotope.filterOut ![Z, Zbig])
def minnormRun : Option D := Z.minnorm 8
def encloseManyRun : Option (Zonotope (Vec D 2)) :=
  Zonotope.encloseMany 8 (fun _ : Fin 1 => Z) ![d 1 0, d 1 0]


/-! ## Discrete-time reach and a network, run rather than only compiled

`LinearSysDT.reach`, `NeurNetContrSysDT.reach` and the hybrid automaton already
have their own examples in `ReachFloat.lean`, compiled but never run; the two
below are run, at a system and a network small enough that a handful of steps
costs nothing. -/

def sys : LinearSysDT D 2 := LinearSysDT.canonical (!![d 15 (-4), d (-1) (-3); d 1 (-3), d 15 (-4)])


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Five reachability steps, order at most `4`. -/
def reachRun : Zonotope (Vec D 2) := sys.reach (S := 𝒵[D]) ⟨Z, Z, 0, 5⟩
    ⟨2, by decide⟩

def net : NeuralNetwork 𝒵[D] 2 2 :=
  .layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer D 2 2) .output)

def encloseRun : Zonotope (Vec D 2) := net.enclose Z

/-- Linear, sigmoid, activation at `Real.sigmoid`, linear, and `net` nested as one layer:
five `Enclose` kinds in one chain, each `eval` over ℝ held `Erased`, which is what this
compiling and running checks. -/
def mixedNet : NeuralNetwork 𝒵[D] 2 2 :=
  .layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2)
    (.layer (⟨2, rfl⟩ : SigmoidLayer D 2 2)
      (.layer (ActivationLayer.of (sigmoidRelaxation_sound (𝕋 := D) 2))
        (.layer (Enclose.pack (S := 𝒵[D]) net)
          (.layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2) .output))))

def mixedEncloseRun : Zonotope (Vec D 2) := mixedNet.enclose Z

/-- `net` at the interval hull representation: the stretch `propagateBounds` pushes bounds
through. -/
def netBox : NeuralNetwork ℐ𝒱[D] 2 2 :=
  .layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer D 2 2) .output)

/-- The bounds `[0, 1]²` of the first layer, met with the bounds `[-1/2, 1/2]²` the next held. -/
def propagateBoundsRun : Interval (Vec D 2) :=
  netBox.propagateBounds ⟨fun _ => d 0 0, fun _ => d 1 0⟩
    (some ⟨fun _ => d (-1) (-1), fun _ => d 1 (-1)⟩)

/-- A fit per order for `findRegionPolys`: the order-1 sigmoid relaxation padded to each
degree, a stand-in that is not sound below order `1`. -/
def regionFit : (o : ℕ) → PolyRelaxation D o := fun o =>
  (sigmoidRelaxation (𝕋 := D) 2).toPoly.padTo o

/-- Stored polynomials of the two infinite ends of `[-4, 4]`. -/
def regionStart : RegionPoly D := ⟨none, some (d (-4) 0), 0, fun _ => d 0 0, d 1 (-1)⟩
def regionEnd : RegionPoly D := ⟨some (d 4 0), none, 0, fun _ => d 1 0, d 1 (-1)⟩

/-- Order `1`, tolerance `1/16`, fuel `64`. -/
def findRegionPolysRun : Option (List (RegionPoly D)) :=
  findRegionPolys regionFit 1 (d 1 (-4)) 64 (d (-4) 0) (d 4 0) regionStart regionEnd

#eval propagateBoundsRun.inf 0
#eval propagateBoundsRun.sup 0
#eval findRegionPolysRun.map List.length

/-- `ctSys` closed around `net`, two control periods of two float steps of `r` each (#1). -/
def nnContrSys : NeurNetContrSys D 𝒵[D] 2 := ⟨ctSys, net⟩
def nnContrReachRun : Zonotope (Vec D 2) := nnContrSys.reachFloat ⟨Z, 0, 2⟩
    ⟨stepR, 2, 4, 2, two_pos⟩
/-- The same loop's set at every period boundary `0, 1, 2`, at an order `reachOrderFloat` finds. -/
def nnContrUnionRun : Option (List (Zonotope (Vec D 2))) :=
  nnContrSys.reachUnionFloat ⟨Z, 0, 2⟩ ⟨stepR, 2, 4, 2, two_pos⟩

#eval reachRun.h
#eval reachRun.c 0
#eval encloseRun.c 0
#eval mixedEncloseRun.c 0
#eval mixedEncloseRun.interval.sup 0
#eval nnContrReachRun.h
#eval nnContrReachRun.c 0
#eval nnContrUnionRun.map (·.length)
#eval ((nnContrUnionRun.getD []).getD 2 Z).c 0
#eval plusBoxRun.sup 0

-- A `SetUnion` of float zonotopes, pushed through `Mtimes`: two branches in, two branches out.
#eval uZ_mtimes.sets.length
#eval (uZ_mtimes.sets.getD 0 Z).c 0

-- The float interval-matrix chain (#1): `e^A`'s enclosure, then a matrix times a box.
#eval expEnclosureRun.inf 0 0
#eval expEnclosureRun.sup 0 0
#eval mtimesIntervalMatRun.inf 0
#eval mtimesIntervalMatRun.sup 0
#eval mtimesIntervalMatZonoRun.c 0
#eval mtimesIntervalMatZonoRun.I_error.sup 0

-- The step matrices (#1, phase 3): an admissible order, then one entry of each box.
#eval stepOrderRun
#eval correctionRun.inf 0 0
#eval correctionRun.sup 0 0
#eval inputTermRun.inf 0 1
#eval inputTermRun.sup 0 1
#eval inputRemainderRun.sup 0 0

-- A continuous-time system sampled in floats (#1): one entry of `[e^{Ar}]`, then five steps.
#eval ctSysD.A.inf 0 0
#eval ctSysD.A.sup 0 0
#eval ctReachRun.h
#eval ctReachRun.c 0
#eval locStepRun.h
#eval locSplitRun.h
#eval locSplitRun.c 0
-- `LinParamSys` over float interval matrices: order, step, input solution, then the windows
#eval lpOrderRun
#eval lpStepRun.h
#eval lpInputRun.c 0
#eval lpReachRun.h
#eval lpReachRun.c 0
#eval lpWindowsRun.map (·.length)
#eval lpWindowsRun.map (·.map (·.h))
#eval lpParticularRun.map (·.h)
#eval (lpParticularRun.getD Z).c 0
#eval lpConstRun.h
#eval lpConstRun.c 0
#eval lpInputWindowsRun.map (·.length)
#eval ((lpInputWindowsRun.getD []).getD 3 Z).c 0
#eval lpSplitWindowsRun.map (·.length)
#eval ((lpSplitWindowsRun.getD []).getD 3 Z).c 0

-- `Alg. 1` of the fully-automated scheme: four windows; then the four error estimates.
#eval manualReachRun.map (·.length)
#eval manualReachRun.map (·.map (·.h))
#eval curvatureErrorRun
#eval intervalErrorRun
#eval pointErrorRun
#eval remainderErrorRun
#eval stepEpsRun.map (·.h)
#eval girardRun.map (·.map (·.h))
#eval errorSolutionRun.h
#eval errorOrderRun
#eval inputTailRun.h
#eval timePointNextRun.c 0

-- Matrix zonotopes in floats (#1): `e^{rA}`'s enclosure, then a sampled reach and an input set.
#eval mzExpRun.h
#eval mzExpRun.c 0 0
#eval mzExpRun.I_error.inf 0 0
#eval mzExpRun.I_error.sup 0 0
#eval ctSysMZ.A.c 0 0
#eval ctMZReachRun.h
#eval ctMZReachRun.c 0
#eval lpMZInputRun.h
#eval lpMZInputRun.c 0


/-! ## A nonlinear system re-linearized in floats (#1)

Van der Pol, `ẋ₁ = x₂`, `ẋ₂ = (1 - x₁²) x₂ - x₁ + u`, from the box `[1.72, 1.78] × [1.22, 1.28]`
under `u ∈ [-1/64, 1/64]`, four steps of `1/32`. The model is interval arithmetic on the field and
on its slopes, `x₁² x₂ - x₁'² x₂' = x₁² (x₂ - x₂') + x₂' (x₁ + x₁') (x₁ - x₁')`, proved to enclose
the real field below, so `reachFloat_outer` holds of the run. -/

section VanDerPol

open SoundFloatArithmetic

/-- The real square's enclosure over `[a, b]`, crude at a sign change but sound. -/
def sqLo (a b : D) : D := Float.Interval.mulLo a b a b
def sqHi (a b : D) : D := Float.Interval.mulHi a b a b

/-- Interval extensions of the field and of its slopes, in `D`. -/
def vdpModel : NonlinearSys.FloatModel D 2 1 where
  f X U :=
    let wl := subDown one (sqHi (X.inf 0) (X.sup 0))                -- 1 - x₁²
    let wh := subUp one (sqLo (X.inf 0) (X.sup 0))
    let pl := Float.Interval.mulLo wl wh (X.inf 1) (X.sup 1)          -- (1 - x₁²) x₂
    let ph := Float.Interval.mulHi wl wh (X.inf 1) (X.sup 1)
    ⟨![X.inf 1, addDown (subDown pl (X.sup 0)) (U.inf 0)],
      ![X.sup 1, addUp (subUp ph (X.inf 0)) (U.sup 0)]⟩
  jacX X _ :=
    let s0 := addDown (X.inf 0) (X.inf 0)                             -- x₁ + x₁'
    let s1 := addUp (X.sup 0) (X.sup 0)
    let ql := Float.Interval.mulLo (X.inf 1) (X.sup 1) s0 s1          -- x₂' (x₁ + x₁')
    let qh := Float.Interval.mulHi (X.inf 1) (X.sup 1) s0 s1
    ⟨!![zero, one; subDown (neg qh) one, subDown one (sqHi (X.inf 0) (X.sup 0))],
      !![zero, one; subUp (neg ql) one, subUp one (sqLo (X.inf 0) (X.sup 0))]⟩
  jacU _ _ := ⟨!![zero; one], !![zero; one]⟩

/-- `x²`'s enclosure, `1 - x²`'s from it. -/
theorem vdp_one_sub_sq_mem {a b : D} {y : ℝ} (h1 : toReal a ≤ y) (h2 : y ≤ toReal b) :
    toReal (subDown one (sqHi a b)) ≤ 1 - y * y ∧
      1 - y * y ≤ toReal (subUp one (sqLo a b)) := by -- --- PROOF ---
  obtain ⟨l, u⟩ := Float.Interval.mul_between_corners h1 h2 h1 h2
  have r1 := subDown_le_sub (one : D) (sqHi a b)
  have r2 := sub_le_subUp (one : D) (sqLo a b)
  rw [toReal_one] at r1 r2
  unfold sqHi sqLo at *
  exact ⟨by linarith, by linarith⟩

/-- `vdpModel` encloses Van der Pol's field and its slopes over every box. -/
theorem vdpModel_encloses : vdpModel.Encloses
    ⟨fun x u => ![x 1, (1 - x 0 * x 0) * x 1 - x 0 + u 0], 2, fun x _ => x⟩ := by -- --- PROOF ---
  refine ⟨fun X U x hx u hu => ?_, fun X U x hx x' hx' u hu u' hu' => ?_⟩
  -- the field: `x₂`, then `(1 - x₁²) x₂ - x₁ + u` in three interval steps
  · have hx0 : toReal (X.inf 0) ≤ (x 0 : ℝ) ∧ (x 0 : ℝ) ≤ toReal (X.sup 0) := hx 0
    have hx1 : toReal (X.inf 1) ≤ (x 1 : ℝ) ∧ (x 1 : ℝ) ≤ toReal (X.sup 1) := hx 1
    have hu0 : toReal (U.inf 0) ≤ (u 0 : ℝ) ∧ (u 0 : ℝ) ≤ toReal (U.sup 0) := hu 0
    obtain ⟨w1, w2⟩ := vdp_one_sub_sq_mem hx0.1 hx0.2
    obtain ⟨p1, p2⟩ := Float.Interval.mul_between_corners w1 w2 hx1.1 hx1.2
    intro i
    fin_cases i
    · exact hx1
    -- both faces: one rounding per interval operation, each the safe way
    · have r1 := addDown_le_add (subDown (Float.Interval.mulLo (subDown one (sqHi (X.inf 0)
        (X.sup 0))) (subUp one (sqLo (X.inf 0) (X.sup 0))) (X.inf 1) (X.sup 1)) (X.sup 0)) (U.inf 0)
      have r2 := subDown_le_sub (Float.Interval.mulLo (subDown one (sqHi (X.inf 0) (X.sup 0)))
        (subUp one (sqLo (X.inf 0) (X.sup 0))) (X.inf 1) (X.sup 1)) (X.sup 0)
      have r3 := add_le_addUp (subUp (Float.Interval.mulHi (subDown one (sqHi (X.inf 0)
        (X.sup 0))) (subUp one (sqLo (X.inf 0) (X.sup 0))) (X.inf 1) (X.sup 1)) (X.inf 0)) (U.sup 0)
      have r4 := sub_le_subUp (Float.Interval.mulHi (subDown one (sqHi (X.inf 0) (X.sup 0)))
        (subUp one (sqLo (X.inf 0) (X.sup 0))) (X.inf 1) (X.sup 1)) (X.inf 0)
      constructor
      · show toReal (addDown (subDown _ (X.sup 0)) (U.inf 0)) ≤ (1 - x 0 * x 0) * x 1 - x 0 + u 0
        linarith [hx0.2, hu0.1]
      · show (1 - x 0 * x 0) * x 1 - x 0 + u 0 ≤ toReal (addUp (subUp _ (X.inf 0)) (U.sup 0))
        linarith [hx0.1, hu0.2]
  -- the slopes: `x₂'(x₁ + x₁')` and `1 - x₁²` boxed, the rest constant
  · have hx0 : toReal (X.inf 0) ≤ (x 0 : ℝ) ∧ (x 0 : ℝ) ≤ toReal (X.sup 0) := hx 0
    have hy0 : toReal (X.inf 0) ≤ (x' 0 : ℝ) ∧ (x' 0 : ℝ) ≤ toReal (X.sup 0) := hx' 0
    have hy1 : toReal (X.inf 1) ≤ (x' 1 : ℝ) ∧ (x' 1 : ℝ) ≤ toReal (X.sup 1) := hx' 1
    have hs1 : toReal (addDown (X.inf 0) (X.inf 0)) ≤ (x 0 : ℝ) + x' 0 :=
      le_trans (addDown_le_add _ _) (add_le_add hx0.1 hy0.1)
    have hs2 : (x 0 : ℝ) + x' 0 ≤ toReal (addUp (X.sup 0) (X.sup 0)) :=
      le_trans (add_le_add hx0.2 hy0.2) (add_le_addUp _ _)
    obtain ⟨q1, q2⟩ := Float.Interval.mul_between_corners hy1.1 hy1.2 hs1 hs2
    obtain ⟨w1, w2⟩ := vdp_one_sub_sq_mem hx0.1 hx0.2
    refine ⟨!![0, 1; -(x' 1 * (x 0 + x' 0)) - 1, 1 - x 0 * x 0], fun q => ?_, !![0; 1],
      fun q => ?_, ?_⟩
    · obtain ⟨i, j⟩ := q
      set qh := Float.Interval.mulHi (X.inf 1) (X.sup 1) (addDown (X.inf 0) (X.inf 0))
        (addUp (X.sup 0) (X.sup 0))
      set ql := Float.Interval.mulLo (X.inf 1) (X.sup 1) (addDown (X.inf 0) (X.inf 0))
        (addUp (X.sup 0) (X.sup 0))
      have n1 := subDown_le_sub (neg qh) (one : D)
      have n2 := sub_le_subUp (neg ql) (one : D)
      rw [toReal_neg, toReal_one] at n1 n2
      -- entry by entry: two constants, then the two boxed slopes
      fin_cases i <;> fin_cases j
      · show toReal (zero : D) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ toReal (zero : D)
        rw [toReal_zero]; exact ⟨le_rfl, le_rfl⟩
      · show toReal (one : D) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ toReal (one : D)
        rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩
      · show toReal (subDown (neg qh) one) ≤ -((x' 1 : ℝ) * (x 0 + x' 0)) - 1
          ∧ -((x' 1 : ℝ) * (x 0 + x' 0)) - 1 ≤ toReal (subUp (neg ql) one)
        constructor <;> linarith
      · exact ⟨w1, w2⟩
    · obtain ⟨i, j⟩ := q
      fin_cases i <;> fin_cases j
      · show toReal (zero : D) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ toReal (zero : D)
        rw [toReal_zero]; exact ⟨le_rfl, le_rfl⟩
      · show toReal (one : D) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ toReal (one : D)
        rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩
    · funext i
      -- each row is the slope identity, ring arithmetic once the sums are written out
      fin_cases i
      · simp [dotProduct]
      · simp [dotProduct]; ring

/-- `[1.72, 1.78] × [1.22, 1.28]`, `1/32` either side of `(7/4, 5/4)`. -/
def vdpX₀ : Zonotope (Vec D 2) :=
  ⟨2, ![d 7 (-2), d 5 (-2)], !![d 1 (-5), d 0 0; d 0 0, d 1 (-5)], zbox 2⟩

/-- `u ∈ [-1/64, 1/64]`. -/
def vdpU : Zonotope (Vec D 1) := ⟨1, ![d 0 0], !![d 1 (-6)], zbox 1⟩

/-- Four re-linearized steps of `1/32`, Taylor order at least `4`, zonotope order `10`. -/
def vdpReach : Option (List (Zonotope (Vec D 2))) :=
  vdpModel.reachFloat { X₀ := vdpX₀, U := vdpU, tFinal := 1 / 8 }
    { Δt := d 1 (-5), η := 4, ρ := 10 }

/-- What a successful run is worth: every run of the real system, over every window. -/
example {Rs : List (Zonotope (Vec D 2))} (h : vdpReach = some Rs) :=
  vdpModel_encloses.reachFloat_outer h

/-- A dyadic read through `Float`, for printing. -/
def vdpF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent

-- The windows' `x₂` ranges, falling at `ẋ₂ ≈ -4.3`, each about `0.2` wide.
#eval vdpReach.map (·.length)
#eval vdpReach.map (·.map fun Z =>
  (vdpF ((Zonotope.interval Z).inf 1), vdpF ((Zonotope.interval Z).sup 1)))

/-! ### The same system with its Hessian: CORA's `'lin'` bound and `'poly'` (#25)

`f₂`'s Hessian in `(x₁, x₂, u)` has `-2x₂` and `-2x₁` off the input block; the model
takes `x₂` at the state and `x₁` at the expansion point, which is what makes the
second-order expansion exact for the cubic term. -/

/-- `[-2b, -2a]` for `y ∈ [a, b]`, `-2y` boxed. -/
def vdpNegTwoLo (b : D) : D := subDown (neg b) b
def vdpNegTwoHi (a : D) : D := subUp (neg a) a

/-- `vdpModel` with the Hessian boxes of both components. -/
def vdpHessModel : NonlinearSys.FloatHessModel D 2 1 :=
  { vdpModel with
    hess := fun X _ => ![⟨fun _ _ => zero, fun _ _ => zero⟩,
      ⟨!![vdpNegTwoLo (X.sup 1), vdpNegTwoLo (X.sup 0), zero;
          vdpNegTwoLo (X.sup 0), zero, zero; zero, zero, zero],
        !![vdpNegTwoHi (X.inf 1), vdpNegTwoHi (X.inf 0), zero;
          vdpNegTwoHi (X.inf 0), zero, zero; zero, zero, zero]⟩] }

/-- Four steps of `1/32` at `alg`, as `vdpReach`. -/
def vdpReachAlg (alg : NonlinearSys.LinReachAlg) : Option (List (Zonotope (Vec D 2))) :=
  vdpHessModel.reachAlgFloat alg { X₀ := vdpX₀, U := vdpU, tFinal := 1 / 8 }
    { Δt := d 1 (-5), η := 4, ρ := 10 }

/-- The slope matrix between two points of a box lies in the model's Jacobian box. -/
theorem vdp_jacX_mem {X : Interval (Vec D 2)} {U : Interval (Vec D 1)} {x x' : Vec ℝ 2}
    (hx : x ∈ X.construct) (hx' : x' ∈ X.construct) :
    !![0, 1; -(x' 1 * (x 0 + x' 0)) - 1, 1 - x 0 * x 0]
      ∈ (vdpModel.jacX X U).construct := by -- --- PROOF ---
  have hx0 : toReal (X.inf 0) ≤ (x 0 : ℝ) ∧ (x 0 : ℝ) ≤ toReal (X.sup 0) := hx 0
  have hy0 : toReal (X.inf 0) ≤ (x' 0 : ℝ) ∧ (x' 0 : ℝ) ≤ toReal (X.sup 0) := hx' 0
  have hy1 : toReal (X.inf 1) ≤ (x' 1 : ℝ) ∧ (x' 1 : ℝ) ≤ toReal (X.sup 1) := hx' 1
  have hs1 : toReal (addDown (X.inf 0) (X.inf 0)) ≤ (x 0 : ℝ) + x' 0 :=
    le_trans (addDown_le_add _ _) (add_le_add hx0.1 hy0.1)
  have hs2 : (x 0 : ℝ) + x' 0 ≤ toReal (addUp (X.sup 0) (X.sup 0)) :=
    le_trans (add_le_add hx0.2 hy0.2) (add_le_addUp _ _)
  obtain ⟨q1, q2⟩ := Float.Interval.mul_between_corners hy1.1 hy1.2 hs1 hs2
  obtain ⟨w1, w2⟩ := vdp_one_sub_sq_mem hx0.1 hx0.2
  intro q
  obtain ⟨i, j⟩ := q
  set qh := Float.Interval.mulHi (X.inf 1) (X.sup 1) (addDown (X.inf 0) (X.inf 0))
    (addUp (X.sup 0) (X.sup 0))
  set ql := Float.Interval.mulLo (X.inf 1) (X.sup 1) (addDown (X.inf 0) (X.inf 0))
    (addUp (X.sup 0) (X.sup 0))
  have n1 := subDown_le_sub (neg qh) (one : D)
  have n2 := sub_le_subUp (neg ql) (one : D)
  rw [toReal_neg, toReal_one] at n1 n2
  -- entry by entry: two constants, then the two boxed slopes
  fin_cases i <;> fin_cases j
  · show toReal (zero : D) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ toReal (zero : D)
    rw [toReal_zero]; exact ⟨le_rfl, le_rfl⟩
  · show toReal (one : D) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ toReal (one : D)
    rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩
  · show toReal (subDown (neg qh) one) ≤ -((x' 1 : ℝ) * (x 0 + x' 0)) - 1
      ∧ -((x' 1 : ℝ) * (x 0 + x' 0)) - 1 ≤ toReal (subUp (neg ql) one)
    constructor <;> linarith
  · exact ⟨w1, w2⟩

/-- `-2y ∈ [-2b, -2a]` for `y ∈ [a, b]`, each end rounded outward. -/
theorem vdp_negTwo_mem {a b : D} {y : ℝ} (h1 : toReal a ≤ y) (h2 : y ≤ toReal b) :
    toReal (vdpNegTwoLo b) ≤ -2 * y ∧ -2 * y ≤ toReal (vdpNegTwoHi a) := by -- --- PROOF ---
  have r1 := subDown_le_sub (neg b) b
  have r2 := sub_le_subUp (neg a) a
  rw [toReal_neg] at r1 r2
  unfold vdpNegTwoLo vdpNegTwoHi
  constructor <;> linarith

/-- `vdpHessModel` encloses Van der Pol to second order: the Jacobian at the point,
and the Hessian with `x₂` at the state and `x₁` at the expansion point. -/
theorem vdpHessModel_encloses : vdpHessModel.Encloses
    ⟨fun x u => ![x 1, (1 - x 0 * x 0) * x 1 - x 0 + u 0], 2, fun x _ => x⟩ where
  toEncloses := vdpModel_encloses
  taylor_mem X U xs us hxs _ x hx u _ := by
    have hp : toRealVec xs ∈ (Interval.point xs).construct := Interval.mem_point (α := Vec D 2) xs
    have hx0 : toReal (X.inf 0) ≤ (toRealVec xs 0 : ℝ) ∧ toRealVec xs 0 ≤ toReal (X.sup 0) := hxs 0
    have hx1 : toReal (X.inf 1) ≤ (x 1 : ℝ) ∧ (x 1 : ℝ) ≤ toReal (X.sup 1) := hx 1
    obtain ⟨a1, a2⟩ := vdp_negTwo_mem hx0.1 hx0.2
    obtain ⟨b1, b2⟩ := vdp_negTwo_mem hx1.1 hx1.2
    refine ⟨_, vdp_jacX_mem (U := Interval.point us) hp hp, !![0; 1], fun q => ?_,
      ![0, !![-2 * x 1, -2 * toRealVec xs 0, 0; -2 * toRealVec xs 0, 0, 0; 0, 0, 0]],
      fun i q => ?_, ?_⟩
    -- the input's Jacobian is constant
    · obtain ⟨i, j⟩ := q
      fin_cases i <;> fin_cases j
      · show toReal (zero : D) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ toReal (zero : D)
        rw [toReal_zero]; exact ⟨le_rfl, le_rfl⟩
      · show toReal (one : D) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ toReal (one : D)
        rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩
    -- the Hessians, entry by entry
    · obtain ⟨j, k⟩ := q
      have z : toReal (zero : D) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ toReal (zero : D) := by
        rw [toReal_zero]; exact ⟨le_rfl, le_rfl⟩
      fin_cases i <;> fin_cases j <;> fin_cases k
      all_goals first
        | exact z
        | exact ⟨b1, b2⟩
        | exact ⟨a1, a2⟩
    -- the expansion, ring arithmetic once the sums are written out
    · funext i
      fin_cases i
      · simp [toRealVec, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.append, Fin.addCases]
      · simp [toRealVec, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.append, Fin.addCases]
        ring

/-- What a successful run is worth, at either `alg`. -/
example {alg : NonlinearSys.LinReachAlg} {Rs : List (Zonotope (Vec D 2))}
    (h : vdpReachAlg alg = some Rs) :=
  vdpHessModel_encloses.reachAlgFloat_outer h

-- `'lin'` with the Hessian, each window about `0.22` wide; `'poly'`, a minute here, is RunCheck's.
#eval (vdpReachAlg .lin).map (·.map fun Z =>
  (vdpF ((Zonotope.interval Z).inf 1), vdpF ((Zonotope.interval Z).sup 1)))

/-! ### The rest of the nonlinear block: centre linearization, adaptive tuning, cubic remainder

`centreAbstrRunFloat` linearizes at the centre of each step's start set, as [Wetzlinger et al.,
HSCC 2021, Alg. 1] does. `adaptRunFloat` is [Wetzlinger et al., 2022, Alg. 1-2]'s loop: each step
chooses its own size from the gain of the last one (`tuneDeltat`'s `optDeltatFloat`,
`estimateGainFloat`, `tuneAbstrOrderFloat`), whatever it chooses `adaptRunFloat_outer` holds. The
tuning constants are `ζ_δ = 1/2`, `ζ_h = ζ_φ = 1/4`, `ζ_Z = 1/8`, `ζ_K = 1/2`. -/

/-- Four steps of `1/32`, each linearized at its start set's centre. -/
def vdpCentreReach : Option (List (Zonotope (Vec D 2))) :=
  vdpModel.centreAbstrRunFloat vdpU { Δt := d 1 (-5), η := 4, ρ := 10 }
    4 vdpX₀

/-- What a successful run is worth: every run of the real system, over every window. -/
example {Rs : List (Zonotope (Vec D 2))} (h : vdpCentreReach = some Rs) :=
  vdpModel_encloses.centreAbstrRunFloat_outer 4 h

#eval vdpCentreReach.map (·.map fun Z =>
  (vdpF ((Zonotope.interval Z).inf 1), vdpF ((Zonotope.interval Z).sup 1)))

/-- The adaptive loop from `vdpX₀` to `t = 1/8`: first horizon `1/32` (a step of `1/16` fails the
region check), last gain `7/8`, order `1`. The options' own step size is not read: every step
takes the one the tuning picked. -/
def vdpAdaptRun : Option (List (NonlinearSys.AdaptState 𝒵[D] 2 ℚ D)) :=
  vdpHessModel.adaptRunFloat vdpU { Δt := d 1 (-5), η := 4, ρ := 10 }
    (d 15 (-4)) (d 7 (-3)) (d 1 (-3)) (d 1 (-1)) 20 20 2 (1 / 8) 4
    (NonlinearSys.adaptInit vdpX₀ (d 1 (-5)) (d 7 (-3)) (d 1 (-6)) 1)

/-- What a successful run is worth: every run of the real system, over each window the tuning
chose. -/
example {ss : List (NonlinearSys.AdaptState 𝒵[D] 2 ℚ D)}
    (h : vdpAdaptRun = some ss) :=
  vdpHessModel_encloses.adaptRunFloat_outer 4 h

-- The times reached, the orders chosen, and each window's `x₂` range: one `#eval`, one run.
#eval vdpAdaptRun.map (·.map fun st =>
  ((st.t, st.κ), (vdpF ((Zonotope.interval st.Rτ).inf 1), vdpF ((Zonotope.interval st.Rτ).sup 1))))

/-- The third derivatives of `f₂` in `(x₁, x₂, u)` are `-2` at the permutations of `(x₁, x₁, x₂)`
and `0` elsewhere; `f₁ = x₂` has none. -/
def vdpThird : Fin 2 → Fin 3 → Mat D 3 3 := fun i j k l =>
  if i = 1 ∧ j.val + k.val + l.val = 1 then d 2 0 else zero

/-- The cubic box over the start set about its centre, in the second coordinate alone. -/
def vdpLagrange : Interval (Vec D 2) :=
  lagrangeRemainderFloat vdpThird (n := 2) (Zonotope.cartProd vdpX₀ vdpU)
    (Fin.append vdpX₀.c vdpU.c)

#eval (vdpF (vdpLagrange.inf 1), vdpF (vdpLagrange.sup 1))

/-! The tuning heuristics on their own: the optimal step for a start radius `1/32` and error
radius `1/64`, and the gain read back from two radii. -/

#eval
  let o := optDeltatFloat (𝕋 := D) 20 20 (d 1 (-1)) (d 1 (-3)) (d 5 (-2)) (d 1 (-2)) (d 1 (-5))
    (d 1 (-6)) (d 1 (-4)) 4
  (vdpF o.1, o.2)
#eval vdpF (estimateGainFloat (d 1 (-1)) (d 4 0) (d 1 (-6)) (d 1 (-7)) 2 10)


end VanDerPol


/-! ## The float sigmoid enclosure tightens with its depth (#114)

`sigmoidEnclosure k` at the point `1`: `σ 1 ≈ 0.7311`. Issue #114 reported `[0.5, 1]` at every
depth; that does not reproduce, the width falling from `0.33` at `k = 0` to under `2⁻¹¹`
at `k = 10` at `Dyadic 24` (where it levels off at `k = 12`, rounding-limited, near `10⁻⁴`), and
at `Dyadic 53` to `2·10⁻⁷` at `k = 20`. Checked by kernel evaluation, over mantissas at the
common exponent `-24`, so a regression to a constant or
depth-ignoring enclosure fails the build. -/

/-- `(lo, hi)` mantissas at exponent `-24` when both ends have that exponent. -/
def sigmoidOneEnds (k : ℕ) : Option (ℤ × ℤ) :=
  let E : Enclosure D := sigmoidEnclosure k
  let lo := E.lo ⟨1, 0⟩
  let hi := E.hi ⟨1, 0⟩
  if lo.exponent = -24 ∧ hi.exponent = -24 then some (lo.mantissa, hi.mantissa) else none

/-- Width at depth `k` below `bound` mantissa units (`2⁻²⁴` each), and `σ 1` bracketed
(`0.7 ≤ lo`, `hi ≤ 0.75`). -/
def sigmoidOneTight (k : ℕ) (bound : ℤ) : Bool :=
  match sigmoidOneEnds k with
  | some (l, h) => decide (h - l < bound ∧ 11744051 ≤ l ∧ h ≤ 12582912)
  | none => false

set_option maxRecDepth 4096 in
example : sigmoidOneTight 10 4096 = true := rfl
set_option maxRecDepth 4096 in
example : sigmoidOneTight 6 65536 = true := rfl
-- Strictly tighter with depth: `k = 4` is not under `10⁵` units, `k = 8` is.
set_option maxRecDepth 4096 in
example : (sigmoidOneTight 4 100000, sigmoidOneTight 8 100000) = (false, true) := rfl


/-! ## A specification check, computed rather than asserted

`Specification.check` at float representations, both instances solver-free: a box safe
set asks `Contains` of the enclosure's interval hull, a halfspace description asks each
row of it (`Contains`) or for one row it lies strictly beyond (`IsDisjoint`). What a
`true` is worth is `NeuralNetwork.holds_of_check`, stated below the runs. -/

/-- Safe: every output coordinate within `[-10, 10]`. -/
def safeBox : Specification (Interval (Vec D 2)) := .safeSet ⟨fun _ => d (-10) 0, fun _ => d 10 0⟩

/-- `x₀ ≥ t` as one row, `-x₀ ≤ -t`, with no equality rows. -/
def halfAbove (t : ℤ) : HPolytope D (Vec D 2) :=
  ⟨1, fun _ j => if j = 0 then d (-1) 0 else d 0 0, fun _ => d (-t) 0, 0, fun i => i.elim0,
    ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

def checkSafe : Bool := safeBox.check encloseRun

/-- `true`: the output never reaches `x₀ ≥ 10`. -/
def checkUnsafeFar : Bool := (Specification.unsafeSet (halfAbove 10)).check encloseRun

/-- `false`: the output does reach `x₀ ≥ 1`, so no row can separate. -/
def checkUnsafeNear : Bool := (Specification.unsafeSet (halfAbove 1)).check encloseRun

/-- A halfspace description safe set, `Z`'s own hull, against `Z` itself. -/
def checkSafeHull : Bool := (Specification.safeSet H).check Z

/-- `Contains` lifted through `SetUnion`, exact: both branches of `uZ`, `Z` and
`Z_mtimes`, lie in `[-10, 10]`. -/
def checkSafeUnion : Bool := safeBox.check uZ

/-- A splitter that never splits, covering trivially: enough to run `verifySplit`. -/
def verifySplitRun : Bool := net.verifySplit safeBox (fun X => (X, X)) 2 Z

/-- What `checkSafe`'s `true` is worth: the specification on the network's exact image. -/
example : safeBox.check (net.enclose Z) →
    (safeBox.Holds (net.eval.out '' ContSet.construct Z)) :=
  net.holds_of_check Z safeBox

#eval checkSafe
#eval checkUnsafeFar
#eval checkUnsafeNear
#eval checkSafeHull
#eval checkSafeUnion
#eval verifySplitRun

/-! ## Softmax's raw lower bound

Three coordinates on `[0, 1/4]`: the normalization alone gives `1 - 2 ru`, the raw lower bound
`(1 + 2 exp (1/4))⁻¹`, both at `k = 10`. -/

def softmaxIn : Interval (Vec D 3) := ⟨fun _ => d 0 0, fun _ => d 1 (-2)⟩

/-- The lower bound `softmaxBox` had before the raw lower bound. -/
def softmaxNormLower : D :=
  maximum zero (subDown one (sumOffUp (0 : Fin 3) fun j => softmaxRawUpper 10 softmaxIn j))

def softmaxRawLowerRun : D := softmaxRawLower 10 softmaxIn 0
def softmaxBoxRun : Interval (Vec D 3) := softmaxBox 10 softmaxIn

#eval softmaxNormLower
#eval softmaxRawLowerRun
#eval (softmaxBoxRun.inf 0)

/-! ## The wrapping-free reach with `box()` in floats

The thesis's `Alg. 2` for `ctSys` from `Z` under the re-centred input `lpInputSet`, at step
`2⁻⁵`, Taylor order `4` and `3` further windows after the first, NaN-gated. -/

def reachBoxRun : Option (List (Zonotope (Vec D 2))) :=
  ctSys.reachBoxFloatChecked Z lpInputSet stepR 4 3

/-! ## The maximal backward reachable set from the inside, in floats

`Alg. 2` of the backward paper for `ctSys`, the target the box polytope `H` (the box of `Z`), the
conversion box that box's own, the input and the disturbance the same small box `backW`, with
step `2⁻⁵`, Taylor order `4` and `t₀ = 0`: the state before the first iteration, after it, and
after two. -/

def backW : Zonotope (Vec D 2) where
  h := 2
  c := ![d 0 0, d 0 0]
  G := !![d 1 (-8), d 0 0; d 0 0, d 1 (-8)]
  I_error := zbox 2

def backBx : Interval (Vec D 2) := Z.interval
def backInitRun : Option (LinearSys.MaxBackReachStateFloat D 2) :=
  ctSys.maxBackReachInitFloat backW backW (d 0 0) 4
def backStepRun : Option (LinearSys.MaxBackReachStateFloat D 2) :=
  backInitRun.bind (ctSys.maxBackReachStepFloat backBx H H backW backW (fun _ _ => backW) stepR 4)
def backRunRun : Option (LinearSys.MaxBackReachStateFloat D 2) :=
  ctSys.maxBackReachRunFloat backBx H H backW backW (fun _ _ => backW) (d 0 0) stepR 4 2

/-! ## Polygons

A triangle, a segment and a point as one-piece polygons: the vertex triangulation of the triangle
(all `3 ^ 3` vertex triples), the quadratic map `x ↦ (xᵀ x, xᵀ x)` of the segment, the mixed map of
the segment and the point, and the polygon an ellipsoid's certified support points span. -/

def polyTri : VPolytope (Vec D 2) :=
    ⟨3, ![![d 0 0, d 0 0], ![d 1 0, d 0 0], ![d 0 0, d 1 0]], zbox 2⟩
def polySeg : VPolytope (Vec D 2) := ⟨2, ![![d 0 0, d 0 0], ![d 1 0, d 0 0]], zbox 2⟩
def polyP : Polygon D := Polygon.ofPieces [polyTri]
def polyS : Polygon D := Polygon.ofPieces [polySeg]
def polyPt : Polygon D := Polygon.ofPieces [⟨1, ![![d 1 0, d 0 0]], zbox 2⟩]
def polyQ : Fin 2 → Mat D 2 2 := fun _ => identityMat D 2
def polyTriangulation : Polygon D := Polygon.triangulation polyP
def polyQuadMap : Polygon D := polyS.quadMap polyQ 0 fun _ _ => false
def polyQuadMapMixed : Polygon D := polyS.quadMapMixed polyPt polyQ 0 fun _ _ => false
def E_polygon : Polygon D :=
  E.polygon [![d 1 0, d 0 0], ![d 0 0, d 1 0], ![d (-1) 0, d 0 0], ![d 0 0, d (-1) 0]]


/-! ## An ellipsoid's bad directions

`Q₁ = 4 I` against `Q₂ = I`: the eigenvalue bound `1/4` certifies the direction `(1, 0)` good
(`sqrt(4)/sqrt(1) = 2` is below `1/λ = 4`). -/

def goodE₁ : Ellipsoid D 2 := ⟨2, ![d 0 0, d 0 0], !![d 2 0, d 0 0; d 0 0, d 2 0], zbox 2⟩
def goodE₂ : Ellipsoid D 2 := ⟨2, ![d 0 0, d 0 0], !![d 1 0, d 0 0; d 0 0, d 1 0], zbox 2⟩
def isGoodDirRun : Bool := goodE₁.isGoodDir goodE₂ ![d 1 0, d 0 0] (d 1 (-2))

/-! ## `ConZonotope.reduceLift`, constraints kept

Four generators in the plane, one inequality `β₀ ≤ ½` and one equality `β₂ + β₃ = 0`, reduced at
order `1`: the lifted zonotope `[G; Aₑ]` has three rows and keeps no generator, so its four are
boxed into `3`, the equality row read back off the box, the inequality row left with the kept
generators and their slack. -/

def cZ_eqs : ConZonotope D (Vec D 2) where
  h := 4
  c := ![d 1 0, d 0 0]
  G := ![![d 1 0, d 0 0], ![d 0 0, d 1 0], ![d 1 (-1), d 1 (-1)], ![d 1 (-2), d (-1) (-1)]]
  P := { m := 1, A := ![![d 1 0, d 0 0, d 0 0, d 0 0]], b := ![d 1 (-1)],
         me := 1, Ae := ![![d 0 0, d 0 0, d 1 0, d 1 0]], be := zbox 1 }
  I_error := zbox 2

def cZ_reduceLift : ConZonotope D (Vec D 2) := cZ_eqs.reduceLift 1

/-! ## Components with a worked example of their own

`Zonotope.and_`, `Polygon.and`, a branch-wise `SetIntersection`, `LevelSet`'s sign test,
a `Taylm` product and sum, the certified `eqBool`, and a nonlinear ARX model simulated in boxes
(`AndFloat`, `SetIntersectionFloat`, `LevelSetFloat`, `TaylmFloat`, `IsequalFloat`,
`NonlinearARXFloat`). `NonlinDASys.reachFloat` is the ordinary run of its float model
(`vdpReach` above) and needs the real-valued reduced model, so it is run in `NonlinDASysFloat`. -/

def zAnd : Zonotope (Vec D 2) := Z.and_ Z_plus
def polyAnd : Polygon D := Polygon.and polyP polyP
/-- The triangle minus the point `(1, 0)`: its edge halfspaces, shifted to the translate. -/
def polyMinkDiff : SetUnion (HPolytope D (Vec D 2)) := Polygon.minkDiff polyP polyPt
/-- The square `[0, 3]²` minus the inner square `[1, 2]²`: one piece per edge of the inner square,
each a box hull of the minuend cut to the side outside that edge. -/
def polySubtract : Polygon D :=
  let sq := fun lo hi : ℤ => (⟨4, ![![d lo 0, d lo 0], ![d hi 0, d lo 0], ![d hi 0, d hi 0],
    ![d lo 0, d hi 0]], zbox 2⟩ : VPolytope (Vec D 2))
  Polygon.subtract (Polygon.ofPieces [sq 0 3]) (Polygon.ofPieces [sq 1 2])
def interSum : SetIntersection (Zonotope (Vec D 2)) :=
  Plus.plus (⟨[Z, Z_plus]⟩ : SetIntersection (Zonotope (Vec D 2))) ⟨[Z]⟩

/-- The sign test of the disc `x² + y² ≤ 1` at bounds `-1/2` on its row value. -/
def lsContainsRun : Bool :=
  LevelSet.containsPoint (𝕋 := D) (⟨1, fun _ => 0, ![.le]⟩ : CORALean.Real.LevelSet 2)
    ![(d (-1) (-1), d (-1) (-1))]

/-- `x · x` and `x · x + x` for the variable `x ∈ [1/2, 3/2]`, order `3`, as ranges (`exp` is run
at `Dyadic 53` in `TaylmFloat`). -/
def tlmI : Interval (Vec D 1) := ⟨![d 1 (-1)], ![d 3 (-1)]⟩
def tlmX : Taylm D 1 := (tlmI.taylm 3) 0
def tlmSq : Taylm D 1 := tlmX.times tlmX
def tlmSum : Taylm D 1 := tlmSq.plus tlmX
def tlmSqBox : Interval D := ⟨tlmSq.bounds.1, tlmSq.bounds.2⟩
def tlmSumBox : Interval D := ⟨tlmSum.bounds.1, tlmSum.bounds.2⟩

/-- `exp (x · x)` at the reduction depth `53`, far above the mantissa width `24`: `expUp`
returns an exponent about `2 ^ 32`, which `addUp` and `le` take without forming `2 ^ gap` (#131).
The range is sound and astronomically wide, so it prints as infinite. -/
def tlmExpDeep : Taylm D 1 := tlmSq.exp 53

def eqBoolRun : Bool := ContSet.eqBool Z Z_plus
def eqBoolSelf : Bool := ContSet.eqBool Z Z

/-- `y(k) = y(k-1)/2 + u(k)`, one lag, as an interval extension of its field. -/
def arxModel : NonlinearARX.FloatModel D 1 1 1 where
  f Y V := ⟨![addDown (half (Y.inf 0)) (V.inf 0)], ![addUp (half (Y.sup 0)) (V.sup 0)]⟩

def arxBoxes : ℕ → Interval (Vec D (1 * 1)) :=
  NonlinearSysDT.simulateBoxFloat arxModel.toNonlinearSysDTFloat ![d 1 0]
    (NonlinearARX.feed 1 fun _ => (![d 1 (-4)] : Vec D 1))
/-! ## A polynomial zonotope's inner approximation and approximate containment

CORA's `innerApprox` example `polyZonotope([0;0],[2 0 2;0 2 2],[0.5;0],[1 0 3;0 1 1])`, inner
boxes down to six bisections; the point `(3/8, 1/4)`, the value at the factors `(0, 1/8, 3/4)`
from which the test starts; and the box of radius `1/64` around it, from a box of radius
`1/32` around those factors. The approximate inverse is `Zonotope.basisInverse`. -/

def pZinner : PolyZonotope (Vec D 2) where
  p := 2
  h := 3
  q := 1
  c := ![d 0 0, d 0 0]
  G := ![![d 2 0, d 0 0], ![d 0 0, d 2 0], ![d 2 0, d 2 0]]
  E := ![![1, 0, 3], ![0, 1, 1]]
  GI := ![![d 1 (-1), d 0 0]]
  I_error := zbox 2
-- the inner boxes, the point and the box
def pZ_innerApprox : List (Zonotope (Vec D 2)) :=
  PolyZonotope.innerApprox pZinner (d 1 (-3)) (fun M => Zonotope.basisInverse M) 20 6
def pZ_containsPointApprox : Bool :=
  PolyZonotope.containsPointApprox pZinner ![d 3 (-3), d 1 (-2)] ![d 0 0, d 1 (-3), d 3 (-2)]
    (fun M => Zonotope.basisInverse M) 20
def pZinnerS : PolyZonotope (Vec D 2) :=
  ⟨0, 0, 2, ![d 3 (-3), d 1 (-2)], Fin.elim0, Fin.elim0, ![![d 1 (-6), d 0 0], ![d 0 0, d 1 (-6)]],
    zbox 2⟩
def pZ_containsSetApprox : Bool :=
  PolyZonotope.containsSetApprox pZinner pZinnerS
    (fun _ => ⟨![d (-1) (-5), d 3 (-5), d 23 (-5)], ![d 1 (-5), d 5 (-5), d 25 (-5)]⟩)
    (fun M => Zonotope.basisInverse M) 20 3
-- the point set test along the four axes: `(8, 0)`, beyond every enclosure, is excluded
def pZ_containsPointSet : Bool :=
  PolyZonotope.containsPointSet pZinner ![![d 3 (-3), d 1 (-2)]] 2 10 fun _ =>
    ⟨4, ![![d 1 0, d 0 0], ![d (-1) 0, d 0 0], ![d 0 0, d 1 0], ![d 0 0, d (-1) 0]]⟩
def pZ_containsPointSetOut : Bool :=
  PolyZonotope.containsPointSet pZinner ![![d 3 (-3), d 1 (-2)], ![d 8 0, d 0 0]] 2 10 fun _ =>
    ⟨4, ![![d 1 0, d 0 0], ![d (-1) 0, d 0 0], ![d 0 0, d 1 0], ![d 0 0, d (-1) 0]]⟩


/-! ## A vertex list away from the origin

The triangle `(1,1), (3,1), (1,3)`: its box is the hull of its vertices, `[1, 3]²`, not that hull
joined with the origin. -/

def polyOffOrigin : VPolytope (Vec D 2) :=
  ⟨3, ![![d 1 0, d 1 0], ![d 3 0, d 1 0], ![d 1 0, d 3 0]], zbox 2⟩
def polyOffOriginBox : Interval (Vec D 2) := polyOffOrigin.interval

end CORALean.RunnableFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
