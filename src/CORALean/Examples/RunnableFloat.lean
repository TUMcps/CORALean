import CORALean.ContDynamics.LinearSysDT.Operations
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
import CORALean.ContSet.ConPolyZono.Float.Instances
import CORALean.ContSet.Ellipsoid.Float.Instances
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.VPolytope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
import CORALean.ContSet.ZonoBundle.Float.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.Enclose
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU

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

Left out, and why: every continuous-time algorithm (`LinearSys`,
`LinParamSys`, `NonlinearSys`, `Location.timeIntervalStep*`) has no float
refinement yet (`pending #1`); `reachErrorFloat`/`reachInnerFloat` are
real-valued guarantee objects, legitimately `spec:`; `HPolytope.zonotope`/
`vPolytopeBox`/`interval`/`conZonotope` and `verifyHalfspace`/`verifyConvex`
each ask for a `FloatBound`/`SupportBound` a solver alone can supply.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RunnableFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 24

/-- `m · 2 ^ e`. -/
def d {p : ℕ} (m e : ℤ) : Dyadic p := ⟨m, e⟩

/-- Zero width in every coordinate. -/
def zbox (n : ℕ) : Interval D n := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


/-! ## Every representation, built or converted to, at `D`

One small zonotope, two generators in two dimensions, and every other
representation reached from it by a `Float/` conversion — exercising the
conversion and supplying the rest of the section a value to run operations on. -/

def Z : Zonotope D 2 where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-2), d 0 0; d 0 0, d 1 (-2)]
  E := zbox 2

def I : Interval D 2 := Z.interval
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

-- `Interval`: `Plus`, `MinkDiff`, `Intersection`, `LinComb`, `Reduce`, `Reindex`, `Mtimes`
def I_plus : Interval D 2 := Plus.plus I I
def I_minkDiff : Interval D 2 := MinkDiff.minkDiff I I
def I_intersection : Interval D 2 := Intersection.intersection I I
def I_linComb : Interval D 2 := LinComb.linComb I I
def I_reduce : Interval D 2 := Reduce.reduce I 1
def I_reindex : Interval D 2 := Reindex.reindex (Equiv.refl (Fin 2)) I
def I_mtimes : Interval D 2 := Mtimes.mtimes (identityMat D 2) I

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


/-! ## The four Box operations `LinearSysDT.reachErrorFloat` sums

Each used to return a `Real.Zonotope`, read back through `toReal`, and so was
`noncomputable`; each now computes in `D` directly. -/

def plusBoxRun : Interval D 2 := Zonotope.plusBox Z Z
def mtimesBoxRun : Interval D 2 := Zonotope.mtimesBox (identityMat D 2) Z
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
  .cons (Layer.linear (S := Zonotope D) (identityMat D 2) (fun _ => d 0 0))
    (.cons Layer.relu .nil)

def encloseRun : Zonotope D 2 := net.enclose Z

#eval reachRun.h
#eval reachRun.c 0
#eval encloseRun.c 0
#eval plusBoxRun.sup 0


/-! ## A specification check, computed rather than asserted

`Zonotope.interval`'s bounds are computed with no solver — a zonotope answers
a direction algebraically — so `I.sup` is a genuine float bound, and
`FloatOps.le` against a threshold is the check a caller runs. -/

/-- Does `Z`'s enclosure stay under `10` in coordinate `0`? -/
def checkSafe : Bool := le (I.sup 0) (d 10 0)

#eval checkSafe

end CORALean.RunnableFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
