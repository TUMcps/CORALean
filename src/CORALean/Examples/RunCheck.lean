import CORALean.Examples.RunnableFloat
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# Every runnable algorithm of `RunnableFloat`, executed

`Examples/RunnableFloat.lean` instantiates the algorithms at `Dyadic 24` as plain `def`s,
which proves each *compiles* at a float scalar. This executable *runs* each of them and prints
one line per `def`, `name | summary | status`, where the summary is a short deterministic
reading of the result (a count, a center, a hull, a Bool) and the status is `ok`, `NAN` (a NaN
reached a result) or `NONE` (an `Option.none` where a value is expected).

`scripts/check-runcheck.sh` diffs the output against `scripts/runcheck-expected.txt` and
checks coverage: every `def` of `RunnableFloat.lean` must be run here, as `RunnableFloat.<name>`
on a line of its own, or listed in `skipped` with a reason. A new runnable algorithm cannot
escape execution.

Hardware `Float` (native binary64) runs a portable subset at the end, the same code at a second
scalar. `Dyadic 24` is the software scalar. The numbers are the demo's: compare, not duplicate,
`scripts/demo-expected.txt`.

Run: `lake exe runcheck` (links, slow) or `lake env lean --run src/CORALean/Examples/RunCheck.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RunCheck

open CORALean CORALean.Float FloatOps

/-- Reads a scalar as a native `Float`, for printing and the NaN test. -/
class ToF (𝕋 : Type) where
  toF : 𝕋 → Float

instance : ToF (Dyadic 24) := ⟨RunnableFloat.vdpF⟩
instance : ToF Float := ⟨id⟩

/-- A summary: the text, every number behind it (for the NaN test), and whether a value is
missing. -/
structure Out where
  text : String
  vals : List Float := []
  missing : Bool := false

section Summaries

variable {𝕋 : Type} [ToF 𝕋]

/-- Six decimals; `-0` as `0`; a number under `10⁻³` as `m*2^e`, which no fixed number of
decimals would show. -/
def fl (x : Float) : String :=
  if x == 0 then "0.000000"
  else if x.isNaN || x.isInf || x.abs ≥ 1e-3 then toString x
  else let (m, e) := x.frExp; s!"{m}*2^{e}"

-- a scalar, then vectors and matrices as lists of `Float`s (for the NaN test) and as text
def sc (x : 𝕋) : String := fl (ToF.toF x)

def vecF {n : ℕ} (v : Vec 𝕋 n) : List Float := List.ofFn fun i => ToF.toF (v i)

def matF {m n : ℕ} (M : Mat 𝕋 m n) : List Float :=
  (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => ToF.toF (M i j)).flatten

def vecS {n : ℕ} (v : Vec 𝕋 n) : String := "(" ++ ", ".intercalate (vecF v |>.map fl) ++ ")"

def matS {m n : ℕ} (M : Mat 𝕋 m n) : String :=
  "[" ++ "; ".intercalate (List.ofFn fun i : Fin m => ", ".intercalate
    (List.ofFn fun j : Fin n => sc (M i j))) ++ "]"

-- boxes and interval matrices: the text, then the numbers behind it
def boxS {n : ℕ} (I : Interval (Vec 𝕋 n)) : String :=
  " x ".intercalate (List.ofFn fun i => "[" ++ sc (I.inf i) ++ ", " ++ sc (I.sup i) ++ "]")

def boxF {n : ℕ} (I : Interval (Vec 𝕋 n)) : List Float := vecF I.inf ++ vecF I.sup

def ofBox {n : ℕ} (I : Interval (Vec 𝕋 n)) : Out := ⟨boxS I, boxF I, false⟩

def ofIMat {m n : ℕ} (M : Interval (Mat 𝕋 m n)) : Out :=
  ⟨"inf " ++ matS M.inf ++ " / sup " ++ matS M.sup,
    matF M.inf ++ matF M.sup, false⟩

end Summaries

section Sets

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToF 𝕋]

-- one summary per representation: its dimensions, its center, an error box, a hull
def zonoF {n : ℕ} (Z : Zonotope 𝕋 n) : List Float :=
  vecF Z.c ++ matF Z.G ++ boxF Z.E ++ boxF Z.interval

def ofZono {n : ℕ} (Z : Zonotope 𝕋 n) : Out :=
  ⟨s!"h={Z.h} c={vecS Z.c} hull={boxS Z.interval}", zonoF Z, false⟩

-- the polytopes and constrained sets
def ofHP {n : ℕ} (P : HPolytope 𝕋 n) : Out :=
  ⟨s!"m={P.m} me={P.me} b={vecS P.b}", matF P.A ++ vecF P.b ++ matF P.Ae ++ boxF P.be, false⟩

def ofVP {n : ℕ} (P : VPolytope 𝕋 n) : Out :=
  ⟨s!"k={P.k} E={boxS P.E}", matF P.V ++ boxF P.E, false⟩

def ofCZ {n : ℕ} (C : ConZonotope 𝕋 n) : Out :=
  ⟨s!"h={C.h} c={vecS C.c} rows={C.P.m} E={boxS C.E}",
    vecF C.c ++ matF C.G ++ matF C.P.A ++ vecF C.P.b ++ boxF C.E, false⟩

def ofPZ {n : ℕ} (P : PolyZonotope 𝕋 n) : Out :=
  ⟨s!"p={P.p} h={P.h} q={P.q} c={vecS P.c} err={boxS P.err}",
    vecF P.c ++ matF P.G ++ matF P.GI ++ boxF P.err, false⟩

def ofCPZ {n : ℕ} (P : ConPolyZono 𝕋 n) : Out :=
  ⟨s!"p={P.p} h={P.h} q={P.q} m={P.m} s={P.s} c={vecS P.c} err={boxS P.err}",
    vecF P.c ++ matF P.G ++ matF P.GI ++ matF P.A ++ boxF P.b ++ boxF P.err, false⟩

-- the remaining representations, and the containers of sets
def ofEll {n : ℕ} (E : Ellipsoid 𝕋 n) : Out :=
  ⟨s!"k={E.k} q={vecS E.q} err={boxS E.err}", vecF E.q ++ matF E.G ++ boxF E.err, false⟩

def ofBundle {n : ℕ} (B : ZonoBundle 𝕋 n) : Out :=
  let hulls := (List.range B.k).filterMap fun i =>
    if h : i < B.k then some (B.Z ⟨i, h⟩) else none
  ⟨s!"k={B.k} members: " ++ "; ".intercalate (hulls.map fun Z => (ofZono Z).text),
    hulls.flatMap zonoF, false⟩

def ofUnion {n : ℕ} (U : SetUnion (Zonotope 𝕋 n)) : Out :=
  ⟨s!"branches={U.sets.length} " ++ "; ".intercalate (U.sets.map fun Z => (ofZono Z).text),
    U.sets.flatMap zonoF, false⟩

-- matrix zonotopes and lists of windows (`none` is a missing value)
def ofMZ {m n : ℕ} (M : MatZonotope 𝕋 m n) : Out :=
  ⟨s!"h={M.h} c={matS M.c} E inf={matS M.E.inf} sup={matS M.E.sup}",
    matF M.c ++ (List.range M.h).flatMap (fun i =>
      if h : i < M.h then matF (M.G ⟨i, h⟩) else []) ++ matF M.E.inf ++ matF M.E.sup, false⟩

def ofWindows {n : ℕ} (o : Option (List (Zonotope 𝕋 n))) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some L =>
    ⟨s!"windows={L.length} last: " ++ (L.getLast?.map fun Z => (ofZono Z).text).getD "-",
      L.flatMap zonoF, L.isEmpty⟩

end Sets

-- the scalar-valued results
def ofBool (b : Bool) : Out := ⟨toString b, [], false⟩
def ofOptNat (o : Option ℕ) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some k => ⟨s!"some {k}", [], false⟩
def ofMat {m n : ℕ} (M : Mat (Dyadic 24) m n) : Out :=
  ⟨matS M, matF M, false⟩
def ofD (x : Dyadic 24) : Out := ⟨sc x, [ToF.toF x], false⟩
def ofWindowsBox (o : Option (List (Zonotope (Dyadic 24) 2))) (i : Fin 2) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some L =>
    ⟨s!"windows={L.length} x{i.val} range per window: " ++
      " ".intercalate (L.map fun Z =>
        s!"[{sc (Z.interval.inf i)}, {sc (Z.interval.sup i)}]"),
      L.flatMap zonoF, L.isEmpty⟩

/-- The status column: a NaN anywhere in the numbers, or a missing value. -/
def status (o : Out) : String :=
  if o.missing then "NONE" else if o.vals.any Float.isNaN then "NAN" else "ok"

/-- Algorithms of `RunnableFloat.lean` with no sensible small input to run, with the reason. -/
def skipped : List (String × String) := []

/-- One output line, and whether it is `ok`. -/
def row (name : String) (o : Out) : StateT Nat IO Unit := do
  let st := status o
  if st != "ok" then modify (· + 1)
  IO.println s!"{name} | {o.text} | {st}"

open RunnableFloat in
/-- Everything `RunnableFloat.lean` defines at `Dyadic 24`, one row per `def`. -/
def dyadicRows : StateT Nat IO Unit := do
  IO.println "== Dyadic 24 =="
  -- scalars and helpers
  row "d" (ofD (RunnableFloat.d 3 (-2)))
  row "zbox" (ofBox (RunnableFloat.zbox 2))
  row "sqLo" (ofD (RunnableFloat.sqLo (RunnableFloat.d (-3) 0) (RunnableFloat.d 2 0)))
  row "sqHi" (ofD (RunnableFloat.sqHi (RunnableFloat.d (-3) 0) (RunnableFloat.d 2 0)))
  row "vdpF" ⟨fl (RunnableFloat.vdpF (RunnableFloat.d 5 (-2))), [], false⟩
  row "vdpNegTwoLo" (ofD (RunnableFloat.vdpNegTwoLo (RunnableFloat.d 3 (-1))))
  row "vdpNegTwoHi" (ofD (RunnableFloat.vdpNegTwoHi (RunnableFloat.d 1 (-1))))
  row "stepR" (ofD RunnableFloat.stepR)
  -- every representation and the conversions
  row "Z" (ofZono RunnableFloat.Z)
  row "I" (ofBox RunnableFloat.I)
  row "V" (ofVP RunnableFloat.V)
  row "cZ" (ofCZ RunnableFloat.cZ)
  row "H" (ofHP RunnableFloat.H)
  row "pZ" (ofPZ RunnableFloat.pZ)
  row "cpZ" (ofCPZ RunnableFloat.cpZ)
  row "E" (ofEll RunnableFloat.E)
  row "zB" (ofBundle RunnableFloat.zB)
  row "H_of_V" (ofHP RunnableFloat.H_of_V)
  row "H_of_cZ" (ofHP RunnableFloat.H_of_cZ)
  row "cZ_of_H" (ofCZ RunnableFloat.cZ_of_H)
  row "V_of_cZ" (ofVP RunnableFloat.V_of_cZ)
  row "cZ_of_V" (ofCZ RunnableFloat.cZ_of_V)
  row "simplex2" (ofHP RunnableFloat.simplex2)
  -- LinearARX and the parallel automaton
  row "arxD" (ofMat RunnableFloat.arxD.toLinearSysDT.A)
  row "arxA" (ofMat RunnableFloat.arxA)
  row "arxB" (ofMat RunnableFloat.arxB)
  row "parP" (ofMat (RunnableFloat.parP.mergeFlows (fun _ => ())).A)
  row "parA" (ofMat RunnableFloat.parA)
  -- the operation classes, one representation at a time
  row "Z_plus" (ofZono RunnableFloat.Z_plus)
  row "Z_linComb" (ofZono RunnableFloat.Z_linComb)
  row "Z_reduce" (ofZono RunnableFloat.Z_reduce)
  row "Z_reindex" (ofZono RunnableFloat.Z_reindex)
  -- the same operations through `SetUnion` and on the intervals
  row "Z_mtimes" (ofZono RunnableFloat.Z_mtimes)
  row "uZ" (ofUnion RunnableFloat.uZ)
  row "uZ_plus" (ofUnion RunnableFloat.uZ_plus)
  row "uZ_reduce" (ofUnion RunnableFloat.uZ_reduce)
  row "uZ_mtimes" (ofUnion RunnableFloat.uZ_mtimes)
  row "I_plus" (ofBox RunnableFloat.I_plus)
  row "I_minkDiff" (ofBox RunnableFloat.I_minkDiff)
  row "I_intersection" (ofBox RunnableFloat.I_intersection)
  row "I_linComb" (ofBox RunnableFloat.I_linComb)
  row "I_reduce" (ofBox RunnableFloat.I_reduce)
  row "I_reindex" (ofBox RunnableFloat.I_reindex)
  row "I_mtimes" (ofBox RunnableFloat.I_mtimes)
  row "matExpA" (ofIMat RunnableFloat.matExpA)
  -- the interval-matrix chain, then the polytopes
  row "expEnclosureRun" (ofIMat RunnableFloat.expEnclosureRun)
  row "mtimesIntervalMatRun" (ofBox RunnableFloat.mtimesIntervalMatRun)
  row "mtimesIntervalMatZonoRun" (ofZono RunnableFloat.mtimesIntervalMatZonoRun)
  row "H_reduce" (ofHP RunnableFloat.H_reduce)
  row "H_intersection" (ofHP RunnableFloat.H_intersection)
  row "V_plus" (ofVP RunnableFloat.V_plus)
  row "V_intersection" (ofVP RunnableFloat.V_intersection)
  row "V_linComb" (ofVP RunnableFloat.V_linComb)
  row "V_reduce" (ofVP RunnableFloat.V_reduce)
  row "V_mtimes" (ofVP RunnableFloat.V_mtimes)
  -- the constrained, polynomial and bundled zonotopes
  row "cZ_plus" (ofCZ RunnableFloat.cZ_plus)
  row "cZ_linComb" (ofCZ RunnableFloat.cZ_linComb)
  row "cZ_reduce" (ofCZ RunnableFloat.cZ_reduce)
  row "pZ_plus" (ofPZ RunnableFloat.pZ_plus)
  row "pZ_linComb" (ofPZ RunnableFloat.pZ_linComb)
  row "pZ_reduce" (ofPZ RunnableFloat.pZ_reduce)
  row "pZ_mtimes" (ofPZ RunnableFloat.pZ_mtimes)
  row "cpZ_plus" (ofCPZ RunnableFloat.cpZ_plus)
  row "cpZ_reduce" (ofCPZ RunnableFloat.cpZ_reduce)
  row "cpZ_intersection" (ofCPZ RunnableFloat.cpZ_intersection)
  row "cpZ_mtimes" (ofCPZ RunnableFloat.cpZ_mtimes)
  -- bundles and ellipsoids
  row "zB_plus" (ofBundle RunnableFloat.zB_plus)
  row "zB_linComb" (ofBundle RunnableFloat.zB_linComb)
  row "zB_intersection" (ofBundle RunnableFloat.zB_intersection)
  row "zB_reduce" (ofBundle RunnableFloat.zB_reduce)
  row "zB_reindex" (ofBundle RunnableFloat.zB_reindex)
  row "zB_mtimes" (ofBundle RunnableFloat.zB_mtimes)
  row "E_mtimes" (ofEll RunnableFloat.E_mtimes)
  -- the continuous-time step matrices
  row "stepA" (ofIMat RunnableFloat.stepA)
  row "stepOrderRun" (ofOptNat RunnableFloat.stepOrderRun)
  row "correctionRun" (ofIMat RunnableFloat.correctionRun)
  row "inputTermRun" (ofIMat RunnableFloat.inputTermRun)
  row "inputRemainderRun" (ofIMat RunnableFloat.inputRemainderRun)
  -- continuous time sampled
  row "ctSys" (ofMat RunnableFloat.ctSys.A)
  row "ctSysD" (ofIMat RunnableFloat.ctSysD.A)
  row "ctReachRun" (ofZono RunnableFloat.ctReachRun)
  row "ctLoc" (ofZono RunnableFloat.ctLoc.inv)
  row "locStepRun" (ofZono RunnableFloat.locStepRun)
  row "locSplitRun" (ofZono RunnableFloat.locSplitRun)
  -- the parametric system
  row "lpA" (ofIMat RunnableFloat.lpA)
  row "lpSys" (ofIMat RunnableFloat.lpSys.A)
  row "lpOrderRun" (ofOptNat RunnableFloat.lpOrderRun)
  row "lpStepRun" (ofZono RunnableFloat.lpStepRun)
  row "lpInputRun" (ofZono RunnableFloat.lpInputRun)
  row "lpReachRun" (ofZono RunnableFloat.lpReachRun)
  row "lpWindowsRun" (ofWindows RunnableFloat.lpWindowsRun)
  -- matrix zonotopes
  row "mzA" (ofMZ RunnableFloat.mzA)
  row "mzExpRun" (ofMZ RunnableFloat.mzExpRun)
  row "ctSysMZ" (ofMZ RunnableFloat.ctSysMZ.A)
  row "ctMZReachRun" (ofZono RunnableFloat.ctMZReachRun)
  row "lpMZSys" (ofMZ RunnableFloat.lpMZSys.A)
  row "lpMZInputRun" (ofZono RunnableFloat.lpMZInputRun)
  -- the four Box operations
  row "plusBoxRun" (ofBox RunnableFloat.plusBoxRun)
  row "mtimesBoxRun" (ofBox RunnableFloat.mtimesBoxRun)
  row "reduceByBoxRun" (ofZono RunnableFloat.reduceByBoxRun)
  row "reduceGirardBoxRun" (ofZono RunnableFloat.reduceGirardBoxRun)
  -- the inputs above absorb nothing; this one absorbs the second generator
  row "reduceByBoxRun (absorbs one)" (ofZono (RunnableFloat.Z.reduceByBox
    (Partition.split 1 1 : Split (Fin RunnableFloat.Z.h) into (Fin 1) ⊕ (Fin 1))))
  -- discrete time and networks
  row "sys" (ofMat RunnableFloat.sys.A)
  row "reachRun" (ofZono RunnableFloat.reachRun)
  -- the network enclosures
  row "net" (ofZono (RunnableFloat.net.enclose RunnableFloat.Z))
  row "encloseRun" (ofZono RunnableFloat.encloseRun)
  row "mixedNet" (ofZono (RunnableFloat.mixedNet.enclose RunnableFloat.Z))
  row "mixedEncloseRun" (ofZono RunnableFloat.mixedEncloseRun)
  row "nnContrSys" (ofMat RunnableFloat.nnContrSys.plant.A)
  row "nnContrReachRun" (ofZono RunnableFloat.nnContrReachRun)
  -- Van der Pol
  row "vdpModel" (ofBox
    (RunnableFloat.vdpModel.f RunnableFloat.vdpX₀.interval RunnableFloat.vdpU.interval))
  row "vdpX₀" (ofZono RunnableFloat.vdpX₀)
  row "vdpU" (ofZono RunnableFloat.vdpU)
  row "vdpReach" (ofWindowsBox RunnableFloat.vdpReach 1)
  row "vdpHessModel" (ofBox (RunnableFloat.vdpHessModel.f RunnableFloat.vdpX₀.interval
    RunnableFloat.vdpU.interval))
  row "vdpReachAlg.lin" (ofWindowsBox (RunnableFloat.vdpReachAlg .lin) 1)
  -- `'poly'` is minutes in the interpreter over the four windows `vdpReachAlg` takes: one window
  row "vdpReachAlg.poly2 (one window)" (ofWindowsBox
    (RunnableFloat.vdpHessModel.reachAlgFloat (.poly 2)
      { R0 := RunnableFloat.vdpX₀, U := RunnableFloat.vdpU, tFinal := 1 / 32 }
      { timeStep := RunnableFloat.d 1 (-5), taylorTerms := 4, zonotopeOrder := 10 }) 1)
  -- sigmoid enclosure depth
  for k in [4, 8, 10] do
    let o := RunnableFloat.sigmoidOneEnds k
    row s!"sigmoidOneEnds {k}" (match o with
      | none => ⟨"none", [], true⟩
      | some (l, h) => ⟨s!"mantissas {l}..{h} width {h - l}", [], false⟩)
  row "sigmoidOneTight" ⟨s!"(10,4096)={RunnableFloat.sigmoidOneTight 10 4096} (4,1e5)=" ++
    s!"{RunnableFloat.sigmoidOneTight 4 100000} (8,1e5)={RunnableFloat.sigmoidOneTight 8 100000}",
    [], false⟩
  -- specifications
  row "safeBox" (ofBox RunnableFloat.safeBox.set)
  row "halfAbove" (ofHP (RunnableFloat.halfAbove 10))
  row "checkSafe" (ofBool RunnableFloat.checkSafe)
  row "checkUnsafeFar" (ofBool RunnableFloat.checkUnsafeFar)
  row "checkUnsafeNear" (ofBool RunnableFloat.checkUnsafeNear)
  row "checkSafeHull" (ofBool RunnableFloat.checkSafeHull)
  row "checkSafeUnion" (ofBool RunnableFloat.checkSafeUnion)
  row "verifySplitRun" (ofBool RunnableFloat.verifySplitRun)

/-! ## Hardware `Float`

A subset of the algorithms above, rebuilt at native binary64: sets and operations, the
discrete-time reach, a network, the continuous-time sampling and a specification check. -/

def floatLit (m e : Int) : Float := Float.scaleB (Float.ofInt m) e

abbrev F := Float

def fzbox (n : ℕ) : Interval (Vec F n) := ⟨fun _ => 0, fun _ => 0⟩

def fZ : Zonotope F 2 where
  h := 2
  c := ![floatLit 1 0, floatLit 0 0]
  G := !![floatLit 1 (-2), 0; 0, floatLit 1 (-2)]
  E := fzbox 2

def fI : Interval (Vec F 2) := fZ.interval
/-- Entries a float cannot hold exactly, so the Box operations have an overshoot to report. -/
def fZ' : Zonotope F 2 where
  h := 2
  c := ![0.1, 0.2]
  G := !![0.3, 0.1; 0.7, 0.9]
  E := fzbox 2

-- a discrete-time system, a network and a continuous-time system sampled, as at `Dyadic 24`
def fSys : LinearSysDT F 2 :=
  ⟨!![floatLit 15 (-4), floatLit (-1) (-3); floatLit 1 (-3), floatLit 15 (-4)]⟩
def fReach : Zonotope F 2 := fSys.reach (S := Zonotope F) ⟨fZ, fZ, 0, 5⟩ ⟨2, by decide⟩
def fNet : NeuralNetwork (Zonotope F) 2 2 :=
  .layer (⟨identityMat F 2, fun _ => 0⟩ : LinearLayer F 2 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer F 2 2) .output)
def fEnclose : Zonotope F 2 := fNet.enclose fZ
def fStepR : F := floatLit 1 (-5)
def fCtSys : LinearSys F 2 := ⟨!![-1, -4; 4, -1]⟩
def fCtD : LinParamSysDT (fun m n => Interval (Mat F m n)) 2 :=
  fCtSys.discretizeEnclosureFloat fStepR 4
def fCtReach : Zonotope F 2 :=
  fCtD.reach (S := Zonotope F) ⟨fZ, fZ, 0, 5⟩ ⟨2, two_pos⟩
def fSafe : Specification (Interval (Vec F 2)) := .safeSet ⟨fun _ => -10, fun _ => 10⟩

-- the rows, in the order of the `Dyadic 24` ones
def floatRows : StateT Nat IO Unit := do
  IO.println "== Float (hardware binary64) =="
  row "Z" (ofZono fZ)
  row "I" (ofBox fI)
  row "Z_plus" (ofZono (fZ.plus fZ))
  row "Z_reduce" (ofZono (fZ.reduce 1))
  row "Z_mtimes" (ofZono (Mtimes.mtimes (identityMat F 2) fZ))
  row "plusBoxRun" (ofBox (Zonotope.plusBox fZ fZ))
  row "mtimesBoxRun" (ofBox (Zonotope.mtimesBox (identityMat F 2) fZ))
  row "reduceGirardBoxRun" (ofZono (Zonotope.reduceGirardBox fZ 1))
  row "plusBoxRun (inexact)" (ofBox (Zonotope.plusBox fZ' fZ'))
  row "mtimesBoxRun (inexact)" (ofBox (Zonotope.mtimesBox !![0.3, 0.7; 0.1, 0.9] fZ'))
  row "reduceGirardBoxRun (inexact)" (ofZono (Zonotope.reduceGirardBox fZ' 1))
  -- reach, network, sampling, specification
  row "reachRun" (ofZono fReach)
  row "encloseRun" (ofZono fEnclose)
  row "ctSysD" (ofIMat fCtD.A)
  row "ctReachRun" (ofZono fCtReach)
  row "checkSafe" (ofBool (fSafe.check fEnclose))

end CORALean.RunCheck


-- =====================================  MAIN DEFINITION  ====================================== --

open CORALean.RunCheck in
def main : IO UInt32 := do
  let ((), bad) ← (do dyadicRows; floatRows : StateT Nat IO Unit).run 0
  IO.println s!"== {bad} row(s) not ok =="
  return if bad = 0 then 0 else 1


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
