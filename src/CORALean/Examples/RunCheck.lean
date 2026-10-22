import CORALean.Examples.Interfaces
import CORALean.Examples.RunnableFloat
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContDynamics.LinearSys.Operations.Canonical
import CORALean.ContDynamics.LinearSysDT.Operations.CanonicalFloat
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Basic
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# Every runnable algorithm of `RunnableFloat`, executed

`Examples/RunnableFloat.lean` instantiates the algorithms at `Dyadic 24` as plain `def`s, which
proves each compiles at a float scalar. This executable runs each of them and prints one line per
`def`, `name | summary | status`: a short deterministic reading of the result, and `ok`, `NAN` (a
NaN reached a result) or `NONE` (an `Option.none` where a value is expected).
`scripts/check-runcheck.sh` diffs the output against `scripts/runcheck-expected.txt` and checks
coverage: every `def` of `RunnableFloat.lean` must be run here, as `RunnableFloat.<name>` on a line
of its own, or listed in `skipped` with a reason. Hardware `Float` runs a portable subset at the
end. Run `lake exe runcheck` or `lake env lean --run src/CORALean/Examples/RunCheck.lean`.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RunCheck

open CORALean CORALean.Float FloatOps

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

/-- A scalar interval: its two bounds. -/
def ofScalarBox (I : Interval 𝕋) : Out :=
  ⟨"[" ++ sc I.inf ++ ", " ++ sc I.sup ++ "]", [ToF.toF I.inf, ToF.toF I.sup], false⟩

def ofIMat {m n : ℕ} (M : Interval (Mat 𝕋 m n)) : Out :=
  ⟨"inf " ++ matS M.inf ++ " / sup " ++ matS M.sup,
    matF M.inf ++ matF M.sup, false⟩

end Summaries

section Sets

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToF 𝕋]

-- one summary per representation: its dimensions, its center, an error box, a hull
def zonoF {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) : List Float :=
  vecF Z.c ++ matF Z.G ++ boxF Z.I_error ++ boxF Z.interval

def ofZono {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) : Out :=
  ⟨s!"h={Z.h} c={vecS Z.c} hull={boxS Z.interval}", zonoF Z, false⟩

-- the polytopes and constrained sets
def ofHP {n : ℕ} (P : HPolytope 𝕋 (Vec 𝕋 n)) : Out :=
  ⟨s!"m={P.m} me={P.me} b={vecS P.b}",
    matF P.A ++ vecF P.b ++ matF P.Ae ++ vecF P.be ++ boxF P.I_error, false⟩

def ofVP {n : ℕ} (P : VPolytope (Vec 𝕋 n)) : Out :=
  ⟨s!"k={P.k} E={boxS P.I_error}", matF P.V ++ boxF P.I_error, false⟩

def ofCZ {n : ℕ} (C : ConZonotope 𝕋 (Vec 𝕋 n)) : Out :=
  ⟨s!"h={C.h} c={vecS C.c} rows={C.P.m} E={boxS C.I_error}",
    vecF C.c ++ matF C.G ++ matF C.P.A ++ vecF C.P.b ++ boxF C.I_error, false⟩

def ofPZ {n : ℕ} (P : PolyZonotope (Vec 𝕋 n)) : Out :=
  ⟨s!"p={P.p} h={P.h} q={P.q} c={vecS P.c} err={boxS P.I_error}",
    vecF P.c ++ matF P.G ++ matF P.GI ++ boxF P.I_error, false⟩

def ofCPZ {n : ℕ} (P : ConPolyZono 𝕋 (Vec 𝕋 n)) : Out :=
  ⟨s!"p={P.p} h={P.h} qI={P.qI} m={P.cons.m} q={P.cons.q} c={vecS P.c} err={boxS P.I_error}",
    vecF P.c ++ matF P.G ++ matF P.GI ++ matF P.cons.A ++ vecF P.cons.b ++ vecF P.cons.b_error
      ++ boxF P.I_error, false⟩

-- the remaining representations, and the containers of sets
def ofEll {n : ℕ} (E : Ellipsoid 𝕋 n) : Out :=
  ⟨s!"q={vecS E.q} Q={matS E.Q} err={boxS E.I_error}",
    vecF E.q ++ matF E.Q ++ boxF E.I_error, false⟩

def ofBundle {n : ℕ} (B : ZonoBundle (Vec 𝕋 n)) : Out :=
  let hulls := (List.range B.k).filterMap fun i =>
    if h : i < B.k then some (B.Z ⟨i, h⟩) else none
  ⟨s!"k={B.k} members: " ++ "; ".intercalate (hulls.map fun Z => (ofZono Z).text),
    hulls.flatMap zonoF, false⟩

/-- The three sets and the time of a minimal backward reachable set's loop state. -/
def ofMinState {n : ℕ} (s : LinearSys.MinBackReachStateOf 𝕋 (Zonotope (Vec 𝕋 n))
    (ConZonotope 𝕋 (Vec 𝕋 n))) :
    Out :=
  ⟨s!"t={sc s.t} ZW0: " ++ (ofZono s.ZW₀).text ++ " ZU0: " ++ (ofZono s.ZU₀).text ++ " R: "
      ++ (ofCZ s.R).text,
    ToF.toF s.t :: zonoF s.ZW₀ ++ zonoF s.ZU₀ ++ (ofCZ s.R).vals, false⟩

/-- The time bracket and the sets of an inner backward reachable set's loop state. -/
def ofMaxState {n : ℕ} (o : Option (LinearSys.MaxBackReachStateFloat 𝕋 n)) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some s =>
    ⟨s!"t=[{sc s.tEnc.inf}, {sc s.tEnc.sup}] ZU: " ++ (ofZono s.ZU).text ++ " UErr=" ++ vecS s.UErr
        ++ " ZW: " ++ (ofZono s.ZW).text ++ " RH: " ++ (ofCZ s.RH).text ++ " RU: "
        ++ (ofZono s.RU).text,
      ToF.toF s.tEnc.inf :: ToF.toF s.tEnc.sup :: zonoF s.ZU ++ vecF s.UErr ++ zonoF s.ZW
        ++ (ofCZ s.RH).vals ++ zonoF s.RU, false⟩

def ofBundles {n : ℕ} (L : List (ZonoBundle (Vec 𝕋 n))) : Out :=
  ⟨s!"bundles={L.length} last: " ++ (L.getLast?.map fun B => (ofBundle B).text).getD "-",
    L.flatMap fun B => (ofBundle B).vals, L.isEmpty⟩

def ofUnion {n : ℕ} (U : SetUnion (Zonotope (Vec 𝕋 n))) : Out :=
  ⟨s!"branches={U.sets.length} " ++ "; ".intercalate (U.sets.map fun Z => (ofZono Z).text),
    U.sets.flatMap zonoF, false⟩

/-- A polygon's piece count and the first piece's vertex count: the pieces that came from a
zonotope have `2 ^ h` corners, too many to list or to bound. -/
def ofPolygon {n : ℕ} (P : SetUnion (VPolytope (Vec 𝕋 n))) : Out :=
  match P.sets.head? with
  | none => ⟨"pieces=0", [], true⟩
  | some p => ⟨s!"pieces={P.sets.length} k={p.k}", [], false⟩

/-- A polygon's piece count and every piece's box hull. -/
def ofPolygonBoxes (P : SetUnion (VPolytope (Vec 𝕋 2))) : Out :=
  ⟨s!"pieces={P.sets.length} " ++ " ".intercalate (P.sets.map fun p => boxS p.interval), [], false⟩

-- probabilistic zonotopes and spectrahedral shadows
def ofProbZ {n : ℕ} (P : ProbZonotope 𝕋 n) : Out :=
  ⟨s!"mean {(ofZono P.Z).text} cov inf={matS P.cov.inf} sup={matS P.cov.sup}",
    zonoF P.Z ++ matF P.cov.inf ++ matF P.cov.sup, false⟩

def ofSpS {n : ℕ} (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : Out :=
  ⟨s!"k={S.k} m={S.m} c={vecS S.c} E={boxS S.I_error}",
    matF S.A₀ ++ vecF S.c ++ matF S.G ++ boxF S.I_error, false⟩
-- the regions of a piecewise polynomial fit: their number, largest error and spans
def ofRegions (o : Option (List (RegionPoly 𝕋))) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some L =>
    let errs := L.map fun r => ToF.toF r.err
    let spans := L.map fun r =>
      s!"[{(r.lo.map sc).getD "-inf"}, {(r.hi.map sc).getD "inf"}]"
    ⟨s!"regions={L.length} max err={fl (errs.foldl max 0)} spans: " ++ " ".intercalate spans,
      errs, L.isEmpty⟩

-- matrix zonotopes and lists of windows (`none` is a missing value)
def ofMZ {m n : ℕ} (M : Zonotope (Mat 𝕋 m n)) : Out :=
  ⟨s!"h={M.h} c={matS M.c} E inf={matS M.I_error.inf} sup={matS M.I_error.sup}",
    matF M.c ++ (List.range M.h).flatMap (fun i =>
      if h : i < M.h then matF (M.G ⟨i, h⟩) else []) ++ matF M.I_error.inf ++ matF M.I_error.sup,
          false⟩

def ofWindows {n : ℕ} (o : Option (List (Zonotope (Vec 𝕋 n)))) : Out :=
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
/-- An exact rational read as a `Float`, for printing. -/
def qF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den
def ofOptZono {n : ℕ} (o : Option (Zonotope (Vec (Dyadic 24) n))) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some Z => ofZono Z
def ofOptStepOrder (o : Option (Dyadic 24 × ℕ)) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some (Δt, η) => ⟨s!"step={sc Δt} order={η}", [ToF.toF Δt], false⟩
/-- A step of the adaptive reach loop: the time it reached, the step taken and the window. -/
def ofAutoStep (o : Option
    (LinearSys.AutoStateFloat (Dyadic 24) 2 × Zonotope (Vec (Dyadic 24) 2))) :
    Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some (s, R) =>
    ⟨s!"t={fl (qF s.t)} step={sc s.Δt} eps_a={fl (qF s.εa)} eps_r={fl (qF s.εr)} window: "
      ++ (ofZono R).text, ToF.toF s.Δt :: zonoF R, false⟩
/-- The windows the adaptive reach loop returns, each with the times it covers. -/
def ofTimedWindows (o : Option (List (ℚ × ℚ × Zonotope (Vec (Dyadic 24) 2)))) : Out :=
  match o with
  | none => ⟨"none", [], true⟩
  | some L =>
    ⟨s!"windows={L.length} spans: " ++ " ".intercalate (L.map fun w =>
        s!"[{fl (qF w.1)}, {fl (qF w.2.1)}]") ++ " last: "
        ++ (L.getLast?.map fun w => (ofZono w.2.2).text).getD "-",
      L.flatMap fun w => zonoF w.2.2, L.isEmpty⟩
def ofWindowsBox (o : Option (List (Zonotope (Vec (Dyadic 24) 2)))) (i : Fin 2) : Out :=
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
  row "expWRun" (ofIMat RunnableFloat.expWRun)
  row "expIntervalWRun" (ofIMat RunnableFloat.expIntervalWRun)
  row "expEnclosureExactRun" (ofIMat RunnableFloat.expEnclosureExactRun)
  row "quadTermRun" (ofScalarBox RunnableFloat.quadTermRun)
  row "quadTermBoundsRun" (ofScalarBox RunnableFloat.quadTermBoundsRun)
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
  row "pZ_convHull" (ofPZ RunnableFloat.pZ_convHull)
  row "pZ_quadMap" (ofPZ RunnableFloat.pZ_quadMap)
  row "pZ_bilin" (ofPZ RunnableFloat.pZ_bilin)
  row "pZ_quadMapMixed" (ofPZ RunnableFloat.pZ_quadMapMixed)
  row "pZ_varInputs" (ofPZ RunnableFloat.pZ_varInputs)
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
  row "probZ" (ofProbZ RunnableFloat.probZ)
  row "probZ_probReduce" (ofProbZ RunnableFloat.probZ_probReduce)
  row "spS" (ofSpS RunnableFloat.spS)
  row "spS_convHull" (ofSpS RunnableFloat.spS_convHull)
  row "spS_or" (ofSpS RunnableFloat.spS_or)
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
  row "ctErrorBoxRun" (ofZono RunnableFloat.ctErrorBoxRun)
  row "ctInputErrorRun" (ofZono RunnableFloat.ctInputErrorRun)
  row "oneStepTpRun" (ofZono RunnableFloat.oneStepTpRun)
  row "oneStepTiRun" (ofZono RunnableFloat.oneStepTiRun)
  row "minkDiffMinuend" (ofZono RunnableFloat.minkDiffMinuend)
  row "minkDiffSubtrahend" (ofZono RunnableFloat.minkDiffSubtrahend)
  row "minkDiffOpt" (ofBool RunnableFloat.minkDiffOpt.isSome)
  row "minkDiffRun" (ofZono RunnableFloat.minkDiffRun)
  row "minkDiffNSMinuend" (ofZono RunnableFloat.minkDiffNSMinuend)
  row "minkDiffNSSubtrahend" (ofZono RunnableFloat.minkDiffNSSubtrahend)
  row "minkDiffNSOpt" (ofBool RunnableFloat.minkDiffNSOpt.isSome)
  row "minkDiffNSRun" (ofZono RunnableFloat.minkDiffNSRun)
  row "minkDiffAlignedOpt" (ofBool RunnableFloat.minkDiffAlignedOpt.isSome)
  row "minkDiffAlignedRun" (ofZono RunnableFloat.minkDiffAlignedRun)
  row "minkDiffStretchRun" (ofZono RunnableFloat.minkDiffStretchRun)
  row "minkDiffStretchInnerOpt" (ofBool RunnableFloat.minkDiffStretchInnerOpt.isSome)
  row "minkDiffStretchInnerRun" (ofZono RunnableFloat.minkDiffStretchInnerRun)
  -- the continuous-time inner approximation (#129)
  row "ctInnerSys" (ofMat RunnableFloat.ctInnerSys.A)
  row "ctInnerX" (ofZono RunnableFloat.ctInnerX)
  row "ctInnerU" (ofZono RunnableFloat.ctInnerU)
  row "ctInnerStep" (ofZono RunnableFloat.ctInnerStep)
  row "ctInnerStepError" (ofZono RunnableFloat.ctInnerStepError)
  row "ctInnerStepOpt" (ofOptZono RunnableFloat.ctInnerStepOpt)
  row "ctInnerStepRun" (ofZono RunnableFloat.ctInnerStepRun)
  row "ctInnerReach" (ofZono RunnableFloat.ctInnerReach)
  row "ctInnerReachError" (ofZono RunnableFloat.ctInnerReachError)
  row "ctInnerReachOpt" (ofOptZono RunnableFloat.ctInnerReachOpt)
  row "ctInnerReachRun" (ofZono RunnableFloat.ctInnerReachRun)
  row "ctLoc" (ofZono RunnableFloat.ctLoc.inv)
  row "locStepRun" (ofZono RunnableFloat.locStepRun)
  row "locSplitRun" (ofZono RunnableFloat.locSplitRun)
  row "hpNormal" (⟨vecS RunnableFloat.hpNormal, vecF RunnableFloat.hpNormal, false⟩ : Out)
  row "hpOffset" (ofD RunnableFloat.hpOffset)
  row "hpBasis" (ofMat RunnableFloat.hpBasis)
  row "zonoGirardUpperRun" (ofD RunnableFloat.zonoGirardUpperRun)
  row "zonoGirardRun" (ofBundle RunnableFloat.zonoGirardRun)
  row "checkFlowRun" (ofWindows (some RunnableFloat.checkFlowRun))
  -- the guard map onto a hyperplane of a location drifting across it
  row "hpMapLoc" (ofZono RunnableFloat.hpMapLoc.U)
  row "hpMapR0" (ofZono RunnableFloat.hpMapR0)
  row "hpMapRun" (ofOptZono RunnableFloat.hpMapRun)
  -- the parametric system
  row "lpA" (ofIMat RunnableFloat.lpA)
  row "lpSys" (ofIMat RunnableFloat.lpSys.A)
  row "lpOrderRun" (ofOptNat RunnableFloat.lpOrderRun)
  row "lpStepRun" (ofZono RunnableFloat.lpStepRun)
  row "lpInputRun" (ofZono RunnableFloat.lpInputRun)
  row "lpReachRun" (ofZono RunnableFloat.lpReachRun)
  row "lpWindowsRun" (ofWindows RunnableFloat.lpWindowsRun)
  row "lpInputSet" (ofZono RunnableFloat.lpInputSet)
  row "lpParticularRun" (ofWindows (RunnableFloat.lpParticularRun.map fun Z => [Z]))
  row "lpConstRun" (ofZono RunnableFloat.lpConstRun)
  row "lpInputWindowsRun" (ofWindows RunnableFloat.lpInputWindowsRun)
  row "lpSplitWindowsRun" (ofWindows RunnableFloat.lpSplitWindowsRun)
  -- matrix zonotopes
  row "mzA" (ofMZ RunnableFloat.mzA)
  row "mzExpRun" (ofMZ RunnableFloat.mzExpRun)
  row "ctSysMZ" (ofMZ RunnableFloat.ctSysMZ.A)
  row "ctMZReachRun" (ofZono RunnableFloat.ctMZReachRun)

/-- The second half of the `Dyadic 24` rows, apart so that each fits the elaborator's budget. -/
def dyadicRows2 : StateT Nat IO Unit := do
  -- the fully-automated scheme's `Alg. 1` and the step error estimates
  row "manualReachRun" (ofWindows RunnableFloat.manualReachRun)
  row "curvatureErrorRun" (ofD RunnableFloat.curvatureErrorRun)
  row "intervalErrorRun" (ofD RunnableFloat.intervalErrorRun)
  row "pointErrorRun" (ofD RunnableFloat.pointErrorRun)
  row "remainderErrorRun" (ofD RunnableFloat.remainderErrorRun)
  row "stepEpsRun" (ofOptZono RunnableFloat.stepEpsRun)
  row "girardRun" (ofWindows RunnableFloat.girardRun)
  row "errorSolutionRun" (ofZono RunnableFloat.errorSolutionRun)
  row "errorOrderRun" (ofOptNat RunnableFloat.errorOrderRun)
  row "inputTailRun" (ofZono RunnableFloat.inputTailRun)
  row "timePointNextRun" (ofZono RunnableFloat.timePointNextRun)
  -- `Alg. 2`, its curvature enclosure and its tuning
  row "constCorrectionRun" (ofIMat RunnableFloat.constCorrectionRun)
  row "curvatureRun" (ofZono RunnableFloat.curvatureRun)
  row "timeIntervalOuterRun" (ofZono RunnableFloat.timeIntervalOuterRun)
  row "errUpRun" (ofD RunnableFloat.errUpRun)
  row "genMinusRun" (ofD RunnableFloat.genMinusRun)
  row "affineErrorRun" (ofD RunnableFloat.affineErrorRun)
  row "particularErrorRun" (ofD RunnableFloat.particularErrorRun)
  row "particularTauErrorRun" (ofD RunnableFloat.particularTauErrorRun)
  row "setOrderRun" (ofOptNat RunnableFloat.setOrderRun)
  row "autoTuneRun" (ofOptStepOrder RunnableFloat.autoTuneRun)
  row "autoStepRun" (ofAutoStep RunnableFloat.autoStepRun)
  row "autoReachRun" (ofTimedWindows RunnableFloat.autoReachRun)
  row "lpMZSys" (ofMZ RunnableFloat.lpMZSys.A)
  row "lpMZInputRun" (ofZono RunnableFloat.lpMZInputRun)
  -- zonotope bundles and backward reachability
  row "bundleRun" (ofBundles RunnableFloat.bundleRun)
  row "minBackInitRun" (ofMinState RunnableFloat.minBackInitRun)
  row "minBackStepRun" (ofMinState RunnableFloat.minBackStepRun)
  row "minBackRunRun" (ofMinState RunnableFloat.minBackRunRun)
  row "minBackSupportRun" (ofD RunnableFloat.minBackSupportRun)
  row "minBackPRun" ⟨s!"({sc (RunnableFloat.minBackPRun 0)}, {sc (RunnableFloat.minBackPRun 1)})",
    [ToF.toF (RunnableFloat.minBackPRun 0), ToF.toF (RunnableFloat.minBackPRun 1)], false⟩
  row "maxBackMuRun" (ofD RunnableFloat.maxBackMuRun)
  row "maxBackPolyRun" (ofHP RunnableFloat.maxBackPolyRun)
  -- the four Box operations
  row "plusBoxRun" (ofBox RunnableFloat.plusBoxRun)
  row "mtimesBoxRun" (ofBox RunnableFloat.mtimesBoxRun)
  row "reduceByBoxRun" (ofZono RunnableFloat.reduceByBoxRun)
  row "reduceGirardBoxRun" (ofZono RunnableFloat.reduceGirardBoxRun)
  -- the inputs above absorb nothing; this one absorbs the second generator
  row "reduceByBoxRun (absorbs one)" (ofZono (RunnableFloat.Z.reduceByBox
    (Partition.split 1 1 : Split (Fin RunnableFloat.Z.h) into (Fin 1) ⊕ (Fin 1))))
  row "mtimesIntervalMatBoxRun" (ofBox RunnableFloat.mtimesIntervalMatBoxRun)
  -- the picks, deletions, bounds and oriented boxes
  row "Zbig" (ofZono RunnableFloat.Zbig)
  row "dominantDirectionsRun" (match RunnableFloat.dominantDirectionsRun with
    | none => ⟨"none", [], true⟩
    | some P => ofMat P)
  row "filterOutRun" ⟨s!"kept {RunnableFloat.filterOutRun.map (·.val)}", [], false⟩
  row "minnormRun" (match RunnableFloat.minnormRun with
    | none => ⟨"none", [], true⟩
    | some x => ofD x)
  row "encloseManyRun" (ofOptZono RunnableFloat.encloseManyRun)
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
  row "nnContrUnionRun" (ofWindows RunnableFloat.nnContrUnionRun)
  row "netBox" (ofBox (RunnableFloat.netBox.enclose RunnableFloat.Z.interval))
  row "propagateBoundsRun" (ofBox RunnableFloat.propagateBoundsRun)
  row "regionFit"
    (ofD ((RunnableFloat.regionFit 1).error (RunnableFloat.d 0 0) (RunnableFloat.d 1 0)))
  row "regionStart" (ofD RunnableFloat.regionStart.err)
  row "regionEnd" (ofD RunnableFloat.regionEnd.err)
  row "findRegionPolysRun" (ofRegions RunnableFloat.findRegionPolysRun)
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
      { X₀ := RunnableFloat.vdpX₀, U := RunnableFloat.vdpU, tFinal := 1 / 32 }
      { Δt := RunnableFloat.d 1 (-5), η := 4, ρ := 10 }) 1)
  -- the rest of the nonlinear block: center linearization, the adaptive loop, the cubic box
  row "vdpCenterReach" (ofWindowsBox RunnableFloat.vdpCenterReach 1)
  row "vdpAdaptRun" (ofWindowsBox (RunnableFloat.vdpAdaptRun.map (List.map (·.Rτ))) 1)
  row "vdpThird" (ofMat (RunnableFloat.vdpThird 1 0))
  row "vdpLagrange" (ofBox RunnableFloat.vdpLagrange)
  -- sigmoid enclosure depth
  for k in [4, 8, 10] do
    let o := RunnableFloat.sigmoidOneEnds k
    row s!"sigmoidOneEnds {k}" (match o with
      | none => ⟨"none", [], true⟩
      | some (l, h) => ⟨s!"mantissas {l}..{h} width {h - l}", [], false⟩)
  row "sigmoidOneTight" ⟨s!"(10,4096)={RunnableFloat.sigmoidOneTight 10 4096} (4,1e5)=" ++
    s!"{RunnableFloat.sigmoidOneTight 4 100000} (8,1e5)={RunnableFloat.sigmoidOneTight 8 100000}",
    [], false⟩
  row "softmaxIn" (ofBox RunnableFloat.softmaxIn)
  row "softmaxNormLower" (ofD RunnableFloat.softmaxNormLower)
  row "softmaxRawLowerRun" (ofD RunnableFloat.softmaxRawLowerRun)
  row "softmaxBoxRun" (ofBox RunnableFloat.softmaxBoxRun)
  -- specifications
  row "safeBox" (ofBox RunnableFloat.safeBox.set)
  row "halfAbove" (ofHP (RunnableFloat.halfAbove 10))
  row "checkSafe" (ofBool RunnableFloat.checkSafe)
  row "checkUnsafeFar" (ofBool RunnableFloat.checkUnsafeFar)
  row "checkUnsafeNear" (ofBool RunnableFloat.checkUnsafeNear)
  row "checkSafeHull" (ofBool RunnableFloat.checkSafeHull)
  row "checkSafeUnion" (ofBool RunnableFloat.checkSafeUnion)
  row "verifySplitRun" (ofBool RunnableFloat.verifySplitRun)
  row "reachBoxRun" (ofWindows RunnableFloat.reachBoxRun)
  row "backW" (ofZono RunnableFloat.backW)
  row "backBx" (ofBox RunnableFloat.backBx)
  row "backInitRun" (ofMaxState RunnableFloat.backInitRun)
  row "backStepRun" (ofMaxState RunnableFloat.backStepRun)
  row "backRunRun" (ofMaxState RunnableFloat.backRunRun)
  -- polygons
  row "polyTri" (ofVP RunnableFloat.polyTri)
  row "polySeg" (ofVP RunnableFloat.polySeg)
  row "polyP" (ofPolygon RunnableFloat.polyP)
  row "polyS" (ofPolygon RunnableFloat.polyS)
  row "polyPt" (ofPolygon RunnableFloat.polyPt)
  row "polyQ" (ofMat (RunnableFloat.polyQ 0))
  row "polyTriangulation" (ofPolygon RunnableFloat.polyTriangulation)
  row "polyQuadMap" (ofPolygon RunnableFloat.polyQuadMap)
  row "polyQuadMapMixed" (ofPolygon RunnableFloat.polyQuadMapMixed)
  row "E_polygon" (ofPolygon RunnableFloat.E_polygon)
  row "goodE₁" (ofEll RunnableFloat.goodE₁)
  row "goodE₂" (ofEll RunnableFloat.goodE₂)
  row "isGoodDirRun" (ofBool RunnableFloat.isGoodDirRun)
  row "cZ_eqs" (ofHP RunnableFloat.cZ_eqs.P)
  row "cZ_reduceLift" (ofCZ RunnableFloat.cZ_reduceLift)
  row "cZ_reduceLift_P" (ofHP RunnableFloat.cZ_reduceLift.P)
  -- the components with a worked example of their own
  row "zAnd" (ofZono RunnableFloat.zAnd)
  row "polyAnd" (ofPolygon RunnableFloat.polyAnd)
  row "polyMinkDiff" ((RunnableFloat.polyMinkDiff.sets.head?.map ofHP).getD ⟨"pieces=0", [], true⟩)
  row "polySubtract" (ofPolygonBoxes RunnableFloat.polySubtract)
  row "interSum" (ofUnion ⟨RunnableFloat.interSum.sets⟩)
  row "lsContainsRun" (ofBool RunnableFloat.lsContainsRun)
  row "tlmI" (ofBox RunnableFloat.tlmI)
  row "tlmX" (ofScalarBox ⟨RunnableFloat.tlmX.bounds.inf, RunnableFloat.tlmX.bounds.sup⟩)
  row "tlmSq" (ofScalarBox ⟨RunnableFloat.tlmSq.bounds.inf, RunnableFloat.tlmSq.bounds.sup⟩)
  row "tlmSum" (ofScalarBox ⟨RunnableFloat.tlmSum.bounds.inf, RunnableFloat.tlmSum.bounds.sup⟩)
  row "tlmSqBox" (ofScalarBox RunnableFloat.tlmSqBox)
  row "tlmSumBox" (ofScalarBox RunnableFloat.tlmSumBox)
  row "tlmExpDeep"
    (ofScalarBox ⟨RunnableFloat.tlmExpDeep.bounds.inf, RunnableFloat.tlmExpDeep.bounds.sup⟩)
  row "eqBoolRun" (ofBool RunnableFloat.eqBoolRun)
  row "eqBoolSelf" (ofBool RunnableFloat.eqBoolSelf)
  row "arxModel" (ofBox (RunnableFloat.arxModel.f
    ⟨fun _ => RunnableFloat.d 1 0, fun _ => RunnableFloat.d 2 0⟩
    ⟨fun _ => RunnableFloat.d 0 0, fun _ => RunnableFloat.d 1 (-4)⟩))
  row "arxBoxes" (ofBox (RunnableFloat.arxBoxes 3))
  -- a polynomial zonotope's inner approximation and approximate containment
  row "pZinner" (ofPZ RunnableFloat.pZinner)
  row "pZ_innerApprox" (ofWindows (some RunnableFloat.pZ_innerApprox))
  row "pZ_containsPointApprox" (ofBool RunnableFloat.pZ_containsPointApprox)
  row "pZinnerS" (ofPZ RunnableFloat.pZinnerS)
  row "pZ_containsSetApprox" (ofBool RunnableFloat.pZ_containsSetApprox)
  row "pZ_containsPointSet" (ofBool RunnableFloat.pZ_containsPointSet)
  row "pZ_containsPointSetOut" (ofBool RunnableFloat.pZ_containsPointSetOut)

/-! ## Hardware `Float`

A subset of the algorithms above, rebuilt at native binary64: sets and operations, the
discrete-time reach, a network, the continuous-time sampling and a specification check. -/

def floatLit (m e : Int) : Float := Float.scaleB (Float.ofInt m) e

abbrev F := Float

def fzbox (n : ℕ) : Interval (Vec F n) := ⟨fun _ => 0, fun _ => 0⟩

def fZ : Zonotope (Vec F 2) where
  h := 2
  c := ![floatLit 1 0, floatLit 0 0]
  G := !![floatLit 1 (-2), 0; 0, floatLit 1 (-2)]
  I_error := fzbox 2

def fI : Interval (Vec F 2) := fZ.interval
/-- Entries a float cannot hold exactly, so the Box operations have an overshoot to report. -/
def fZ' : Zonotope (Vec F 2) where
  h := 2
  c := ![0.1, 0.2]
  G := ![![0.3, 0.7], ![0.1, 0.9]]
  I_error := fzbox 2

-- a discrete-time system, a network and a continuous-time system sampled, as at `Dyadic 24`
def fSys : LinearSysDT F 2 :=
  LinearSysDT.canonicalFloat
    !![floatLit 15 (-4), floatLit (-1) (-3); floatLit 1 (-3), floatLit 15 (-4)]
def fReach : Zonotope (Vec F 2) := fSys.reach (S := 𝒵[F]) ⟨fZ, fZ, 0, 5⟩
    ⟨2, by decide⟩
def fNet : NeuralNetwork 𝒵[F] 2 2 :=
  .layer (⟨identityMat F 2, fun _ => 0⟩ : LinearLayer F 2 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer F 2 2) .output)
def fEnclose : Zonotope (Vec F 2) := fNet.enclose fZ
def fStepR : F := floatLit 1 (-5)
def fCtSys : LinearSys F 2 := LinearSys.canonical !![-1, -4; 4, -1]
def fCtD : LinParamSysDT ℐ[F] 2 :=
  fCtSys.discretizeEnclosureFloat fStepR 4
def fCtReach : Zonotope (Vec F 2) :=
  fCtD.reach (S := 𝒵[F]) ⟨fZ, fZ, 0, 5⟩ ⟨2, two_pos⟩
def fSafe : Specification (Interval (Vec F 2)) := .safeSet ⟨fun _ => -10, fun _ => 10⟩

-- the rows, in the order of the `Dyadic 24` ones
def floatRows : StateT Nat IO Unit := do
  IO.println "== Float (hardware binary64) =="
  row "Z" (ofZono fZ)
  row "I" (ofBox fI)
  row "Z_plus" (ofZono (fZ.plus fZ))
  row "Z_reduce" (ofZono (fZ.reduce 1))
  row "Z_mtimes" (ofZono (Mtimes.mtimes (S := 𝒵[F]) (identityMat F 2) fZ))
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
  row "polyOffOrigin" (ofVP RunnableFloat.polyOffOrigin)
  row "polyOffOriginBox" (ofBox RunnableFloat.polyOffOriginBox)

end CORALean.RunCheck


-- =====================================  MAIN DEFINITION  ====================================== --

open CORALean.RunCheck in
def main : IO UInt32 := do
  let ((), bad) ← (do dyadicRows; dyadicRows2; floatRows : StateT Nat IO Unit).run 0
  IO.println s!"== {bad} row(s) not ok =="
  return if bad = 0 then 0 else 1


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
