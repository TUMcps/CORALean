import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
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
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.VPolytope.Float.Instances
import CORALean.ContSet.ZonoBundle.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
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
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Theorems.SigmoidRelaxationSound
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.Enclose
import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Theorems.HoldsOfCheck
import CORALean.Specification.Instances

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

Left out, and why: `LinearSys`'s float runs are run in `RotationFloat`; the other
continuous-time algorithms (`LinParamSys`, `NonlinearSys`, `Location.timeIntervalStep*`)
have no float refinement yet (`pending #1`), only their steps' matrices; `reachErrorFloat`/
`reachInnerFloat` are real-valued guarantee objects, legitimately `spec:`;
`HPolytope.zonotope`/`vPolytopeBox`/`interval`/`conZonotope` and `verifyHalfspace`/
`verifyConvex` each ask for a `FloatBound`/`SupportBound` a solver alone can supply.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


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

def Z : Zonotope D 2 where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-2), d 0 0; d 0 0, d 1 (-2)]
  E := zbox 2

def I : Interval (Vec D 2) := Z.interval
def V : VPolytope D 2 := Z.vPolytope
def cZ : ConZonotope D 2 := Z.conZonotope
def H : HPolytope D 2 := Z.hPolytope (identityMat D 2)
def pZ : PolyZonotope D 2 := I.polyZonotope
def cpZ : ConPolyZono D 2 := cZ.conPolyZono
def E : Ellipsoid D 2 := I.ellipsoid (d 1 0)
def zB : ZonoBundle D 2 := ⟨1, fun _ => Z⟩

-- more conversions, at the representations `Z`, `I`, `V`, `cZ` above already supply

def H_of_V : HPolytope D 2 := V.hPolytope (identityMat D 2)
def H_of_cZ : HPolytope D 2 := cZ.hPolytope (identityMat D 2)
def cZ_of_H : ConZonotope D 2 := H.onCoefficients Z |>.conZonotopeOf Z
def V_of_cZ : VPolytope D 2 := cZ.vPolytopeBox
def cZ_of_V : ConZonotope D 2 := V.conZonotope
def simplex2 : HPolytope D 2 := VPolytope.simplex D 2


/-! ## Every operation class each representation above instantiates -/

-- `Zonotope`: `Plus`, `LinComb`, `Reduce`, `Reindex`, `Mtimes`
def Z_plus : Zonotope D 2 := Z.plus Z
def Z_linComb : Zonotope D 2 := LinComb.linComb Z Z
def Z_reduce : Zonotope D 2 := Z.reduce 1
def Z_reindex : Zonotope D 2 := Reindex.reindex (Equiv.refl (Fin 2)) Z
def Z_mtimes : Zonotope D 2 := Mtimes.mtimes (identityMat D 2) Z

-- `SetUnion (Zonotope D)`: `Plus`, `Reduce`, `Mtimes`, generic over the member type
def uZ : SetUnion (Zonotope D 2) := ⟨[Z, Z_mtimes]⟩
def uZ_plus : SetUnion (Zonotope D 2) := Plus.plus uZ uZ
def uZ_reduce : SetUnion (Zonotope D 2) := Reduce.reduce uZ 1
def uZ_mtimes : SetUnion (Zonotope D 2) :=
  Mtimes.mtimes (S := fun n => SetUnion (Zonotope D n)) (identityMat D 2) uZ

-- `Interval`: `Plus`, `MinkDiff`, `Intersection`, `LinComb`, `Reduce`, `Reindex`, `Mtimes`
def I_plus : Interval (Vec D 2) := Plus.plus I I
def I_minkDiff : Interval (Vec D 2) := MinkDiff.minkDiff I I
def I_intersection : Interval (Vec D 2) := Intersection.intersection I I
def I_linComb : Interval (Vec D 2) := LinComb.linComb I I
def I_reduce : Interval (Vec D 2) := Reduce.reduce I 1
def I_reindex : Interval (Vec D 2) :=
  Reindex.reindex (S := fun n => Interval (Vec D n)) (Equiv.refl (Fin 2)) I
def I_mtimes : Interval (Vec D 2) :=
  Mtimes.mtimes (S := fun n => Interval (Vec D n)) (identityMat D 2) I


/-! ## The float interval-matrix chain: `matMul`/`matPow`/`smul`/`expIntervalEnclosure`

A point interval matrix, its float `expIntervalEnclosure`, and an interval
matrix times a box through the interval-matrix `Mtimes` instance (#1, phase 2). -/

def matExpA : Interval (Mat D 2 2) :=
  ⟨!![d 0 0, d 1 (-1); d (-1) (-1), d 0 0], !![d 0 0, d 1 (-1); d (-1) (-1), d 0 0]⟩

def expEnclosureRun : Interval (Mat D 2 2) := MatExp.expIntervalEnclosure matExpA 4

def mtimesIntervalMatRun : Interval (Vec D 2) :=
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat D m n)) (S := fun n => Interval (Vec D n))
    matExpA I

-- the same interval matrix, at `expEnclosureRun`, times a float zonotope (#1, phase 3 prep)
def mtimesIntervalMatZonoRun : Zonotope D 2 :=
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat D m n)) (S := Zonotope D) expEnclosureRun Z

-- `HPolytope`: `Reduce`, `Intersection`
def H_reduce : HPolytope D 2 := Reduce.reduce H 1
def H_intersection : HPolytope D 2 := Intersection.intersection H H

-- `VPolytope`: `Plus`, `Intersection`, `LinComb`, `Reduce`, `Mtimes`
def V_plus : VPolytope D 2 := Plus.plus V V
def V_intersection : VPolytope D 2 := Intersection.intersection V V
def V_linComb : VPolytope D 2 := LinComb.linComb V V
def V_reduce : VPolytope D 2 := Reduce.reduce V 1
def V_mtimes : VPolytope D 2 := Mtimes.mtimes (identityMat D 2) V

-- `ConZonotope`: `Plus`, `LinComb`, `Reduce`
def cZ_plus : ConZonotope D 2 := Plus.plus cZ cZ
def cZ_linComb : ConZonotope D 2 := LinComb.linComb cZ cZ
def cZ_reduce : ConZonotope D 2 := Reduce.reduce cZ 1

-- `PolyZonotope`: `Plus`, `LinComb`, `Reduce`, `Mtimes`
def pZ_plus : PolyZonotope D 2 := Plus.plus pZ pZ
def pZ_linComb : PolyZonotope D 2 := LinComb.linComb pZ pZ
def pZ_reduce : PolyZonotope D 2 := Reduce.reduce pZ 1
def pZ_mtimes : PolyZonotope D 2 := Mtimes.mtimes (identityMat D 2) pZ

-- `ConPolyZono`: `Plus`, `Reduce`, `Intersection`, `Mtimes`
def cpZ_plus : ConPolyZono D 2 := Plus.plus cpZ cpZ
def cpZ_reduce : ConPolyZono D 2 := Reduce.reduce cpZ 1
def cpZ_intersection : ConPolyZono D 2 := Intersection.intersection cpZ cpZ
def cpZ_mtimes : ConPolyZono D 2 := Mtimes.mtimes (identityMat D 2) cpZ

-- `ZonoBundle`: `Plus`, `LinComb`, `Intersection`, `Reduce`, `Reindex`, `Mtimes`
def zB_plus : ZonoBundle D 2 := Plus.plus zB zB
def zB_linComb : ZonoBundle D 2 := LinComb.linComb zB zB
def zB_intersection : ZonoBundle D 2 := Intersection.intersection zB zB
def zB_reduce : ZonoBundle D 2 := Reduce.reduce zB 1
def zB_reindex : ZonoBundle D 2 := Reindex.reindex (Equiv.refl (Fin 2)) zB
def zB_mtimes : ZonoBundle D 2 := Mtimes.mtimes (identityMat D 2) zB

-- `Ellipsoid`: `Mtimes` alone — the rest of its operations have no float file yet
def E_mtimes : Ellipsoid D 2 := Mtimes.mtimes (identityMat D 2) E


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


/-! ## The four Box operations `LinearSysDT.reachErrorFloat` sums

Each used to return a `Real.Zonotope`, read back through `toReal`, and so was
`noncomputable`; each now computes in `D` directly. -/

def plusBoxRun : Interval (Vec D 2) := Zonotope.plusBox Z Z
def mtimesBoxRun : Interval (Vec D 2) := Zonotope.mtimesBox (identityMat D 2) Z
def reduceByBoxRun : Zonotope D 2 :=
  Z.reduceByBox (Partition.split 2 0 : Split (Fin Z.h) into (Fin 2) ⊕ (Fin 0))
def reduceGirardBoxRun : Zonotope D 2 := Zonotope.reduceGirardBox Z 1


/-! ## Discrete-time reach and a network, run rather than only compiled

`LinearSysDT.reach`, `NeurNetContrSysDT.reach` and the hybrid automaton already
have their own examples in `ReachFloat.lean`, compiled but never run; the two
below are run, at a system and a network small enough that a handful of steps
costs nothing. -/

def sys : LinearSysDT D 2 := ⟨!![d 15 (-4), d (-1) (-3); d 1 (-3), d 15 (-4)]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Five reachability steps, order at most `4`. -/
def reachRun : Zonotope D 2 := sys.reach (S := Zonotope D) 2 (by decide) Z Z 5

def net : NeuralNetwork (Zonotope D) 2 2 :=
  .layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer D 2 2) .output)

def encloseRun : Zonotope D 2 := net.enclose Z

/-- Linear, sigmoid, activation at `Real.sigmoid`, linear, and `net` nested as one layer:
five `Enclose` kinds in one chain, each `eval` over ℝ held `Erased`, which is what this
compiling and running checks. -/
def mixedNet : NeuralNetwork (Zonotope D) 2 2 :=
  .layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2)
    (.layer (⟨2, rfl⟩ : SigmoidLayer D 2 2)
      (.layer (ActivationLayer.of (sigmoidRelaxation_sound (𝕋 := D) 2))
        (.layer (Enclose.pack (S := Zonotope D) net)
          (.layer (⟨identityMat D 2, fun _ => d 0 0⟩ : LinearLayer D 2 2) .output))))

def mixedEncloseRun : Zonotope D 2 := mixedNet.enclose Z

#eval reachRun.h
#eval reachRun.c 0
#eval encloseRun.c 0
#eval mixedEncloseRun.c 0
#eval mixedEncloseRun.interval.sup 0
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
#eval mtimesIntervalMatZonoRun.E.sup 0

-- The step matrices (#1, phase 3): an admissible order, then one entry of each box.
#eval stepOrderRun
#eval correctionRun.inf 0 0
#eval correctionRun.sup 0 0
#eval inputTermRun.inf 0 1
#eval inputTermRun.sup 0 1
#eval inputRemainderRun.sup 0 0


/-! ## A specification check, computed rather than asserted

`Specification.check` at float representations, both instances solver-free: a box safe
set asks `Contains` of the enclosure's interval hull, a halfspace description asks each
row of it (`Contains`) or for one row it lies strictly beyond (`IsDisjoint`). What a
`true` is worth is `NeuralNetwork.holds_of_check`, stated below the runs. -/

/-- Safe: every output coordinate within `[-10, 10]`. -/
def safeBox : Specification (Interval (Vec D 2)) := .safeSet ⟨fun _ => d (-10) 0, fun _ => d 10 0⟩

/-- `x₀ ≥ t` as one row, `-x₀ ≤ -t`, with no equality rows. -/
def halfAbove (t : ℤ) : HPolytope D 2 :=
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

end CORALean.RunnableFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
