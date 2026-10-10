import CORALean.Examples.Bench.FirstStepJson
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.RandVerifyDistance
import CORALean.Examples.Bench.RandVerifyHull
import CORALean.Examples.Bench.RandVerifyJob
import CORALean.Examples.Bench.RandVerifyNumber
import CORALean.Examples.Bench.RandVerifyOutExact
import CORALean.Examples.Bench.RandVerifyRead
import CORALean.Examples.Bench.RandVerifyReach
import CORALean.Examples.Bench.RandVerifySci
import CORALean.Examples.Bench.RandVerifySeparation
import CORALean.Examples.Bench.RandVerifyUnsafe
import CORALean.Examples.Bench.RandVerifyWindowOf

/-!
# `randverify`: instances sharing one system, one number type, one algorithm

The system of `J.inst` is read exactly (`readRandSystem`; a format that cannot hold it is `"none"`)
and reached ONCE; every instance of `insts`, all stating that system, is checked against the same
windows, one record each, in order.

Each window is mapped to output space exactly, `Y = C · R` over ℚ (`outputZonoExact`), and each
unsafe box, rounded outward into the format, tested against it by `separation`, the exact
separating-axis test: `verified` iff every box misses every window. `distances` gives per box the
signed distance (`sign`, `value`, the closest `window`), `distances_unrounded` the same for the
file's own boxes, and `unverifiable_from_rounding[j]` says box `j` is separated there and not here.
The former test, the interval hull of `Y` (`signedDistance`), is kept as `verified_hull`,
`distances_hull` and `distances_hull_unrounded`. `status` is `"ok"`, `"none"` with a `reason`, or
`"overflow-NaN"` (a bound, window or hull past the format's range, `verified: false`).
`time_reach_ms` is the wall clock of the reach and the exact windows, shared by the `reach_shared`
instances; `time_check_ms` this instance's tests; `time_ms` their sum.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_optRat : Option ℚ → Json
  | some q => ratJson q
  | none => Json.null

/-- A separation result: the sign of the distance, its value, the closest window. -/
def aux_sepJson : Option (Bool × Float × ℕ) → Json
  | some (_, v, k) => Json.mkObj [("sign", Json.str (if v > 0 then "+" else if v < 0 then "-"
      else "0")), ("value", Json.str (sciString v)), ("window", Lean.toJson k)]
  | none => Json.null

def aux_sepPos : Option (Bool × Float × ℕ) → Bool
  | some (s, _, _) => s
  | none => false

/-- The `params` the record echoes. -/
def aux_paramsJson (J : RandJob) : Json :=
  Json.mkObj [("dt", Json.str J.dt), ("eta", Lean.toJson J.eta), ("order", Lean.toJson J.rho),
    ("tend", ratJson J.inst.tend)]

/-- Every stored number of `R`. -/
def aux_entries (R : Zonotope 𝕋 5) : List 𝕋 :=
  (List.finRange 5).flatMap fun i =>
    [R.c i, R.E.inf i, R.E.sup i] ++ (List.finRange R.h).map fun j => R.G j i

/-- The windows, whether any is past the range, the exact windows and the hulls over ℚ. -/
def aux_reachAll (nonFinite : 𝕋 → Bool) (J : RandJob) (S : RandSystem 𝕋) :
    Except String (ℕ × Bool × List RandWindow × List (Array (ℚ × ℚ))) := do
  let Rs ← randVerifyReach J.alg S J.inst.tend J.eta J.rho
  let hulls := outputHulls S.C Rs
  let bad := hulls.any (fun H =>
    (List.finRange 2).any fun i => nonFinite (H.inf i) || nonFinite (H.sup i)) ||
    Rs.any fun R => (aux_entries R).any nonFinite
  -- an infinite or `NaN` window has no distance
  if bad then pure (Rs.length, true, [], []) else
  let ws := Rs.map fun R => windowOf (outputZonoExact J.inst.C R)
  let hq := hulls.map fun H =>
    Array.ofFn fun i : Fin 2 => (ToRat.toRat (H.inf i), ToRat.toRat (H.sup i))
  pure (Rs.length, false, ws, hq)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The records; `head` is `firstStepHead`'s `type`, `format`, `significand_bits`. -/
def randVerifyRecords (head : List (String × Json)) (nt : NumberType 𝕋)
    (inst : String → ExactDyadic → Except String 𝕋) (exactIn : ExactDyadic → 𝕋) (J : RandJob)
    (insts : Array RandInstance) : IO (Array Json) := do
  -- what a record that got no distances says
  let nonFinite : 𝕋 → Bool := nt.overflows.getD fun _ => false
  let nulls : List (String × Json) := [("distances", Json.null), ("distances_unrounded", Json.null),
    ("distances_hull", Json.null), ("distances_hull_unrounded", Json.null),
    ("unverifiable_from_rounding", Json.null), ("windows", Json.null), ("time_ms", Json.null)]
  let finish (I : RandInstance) (status reason : String) (verified : Json)
      (extra : List (String × Json)) : Json :=
    Json.mkObj (head ++ [("instance", Json.str I.name), ("algorithm", Json.str J.alg.name),
      ("status", Json.str status), ("reason", Json.str reason), ("verified", verified)] ++
      extra ++ [("params", aux_paramsJson { J with inst := I })])
  match parseRandString J.dt with
  | .error e => pure (insts.map fun I => finish I "none" s!"dt: {e}" Json.null nulls)
  | .ok dtQ =>
  match readRandSystem inst exactIn J.inst dtQ with
  | .error e => pure (insts.map fun I => finish I "none" s!"not representable: {e}" Json.null nulls)
  | .ok S =>
  -- the reach, once, with the exact windows; forced before the clock stops
  let t0 ← IO.monoNanosNow
  let res := aux_reachAll nonFinite J S
  match res with
  | .ok (_, _, ws, _) =>
    let cs : ℕ := ws.foldl (fun a W => a + W.den + W.normals.size) 0
    if cs = 4242424242424242 then IO.eprintln "randverify: checksum" else pure ()
  | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  let msReach := ((t1 - t0 : ℕ).toFloat) / 1000000.0
  let shared := [("time_reach_ms", Lean.toJson msReach), ("reach_shared", Lean.toJson insts.size),
    ("x0_enclosed", Json.bool S.x0Enclosed)]
  -- every instance against the same windows
  insts.mapM fun I => do
    -- the unsafe boxes, rounded outward into the format
    let uns := I.unsafeSets.map (roundUnsafeOut exactIn)
    let flags := ("unsafe_rounded", Json.arr (uns.map fun s => Json.arr (s.map fun (_, _, a, b) =>
      Json.mkObj [("lb", Json.bool a), ("ub", Json.bool b)])))
    if uns.any (·.any fun (l, h, _, _) => nonFinite l || nonFinite h) then
      return finish I "overflow-NaN" "an unsafe bound rounds out of the format's range"
        (Json.bool false) (flags :: nulls)
    match res with
    | .error e =>
      return finish I "none" e Json.null ((flags :: nulls.filter (·.1 ≠ "time_ms")) ++
        [("time_ms", Lean.toJson msReach)] ++ shared)
    | .ok (n, true, _, _) =>
      return finish I "overflow-NaN" "a window or output hull is past the format's range or NaN"
        (Json.bool false) ([flags, ("windows", Lean.toJson n),
          ("time_ms", Lean.toJson msReach)] ++ shared ++
          nulls.filter (·.1 ∉ ["windows", "time_ms"]))
    | .ok (n, false, ws, hq) =>
      -- the exact tests and the hull distances, against the rounded and the file's own boxes
      let unsQ := uns.map (·.map fun (l, h, _, _) => (ToRat.toRat l, ToRat.toRat h))
      let c0 ← IO.monoNanosNow
      let ds := unsQ.map (separation ws)
      -- the file's own box, unless rounding moved none of its bounds
      let du := (I.unsafeSets.zip (uns.zip ds)).map fun (S, s, d) =>
        if s.any (fun (_, _, a, b) => a || b) then separation ws S else d
      let dh := unsQ.map (signedDistance hq)
      let dhu := I.unsafeSets.map (signedDistance hq)
      let cs : ℕ := (ds ++ du).foldl (fun a d => a + (aux_sepJson d).compress.length) 0 +
        (dh ++ dhu).foldl (fun a d => a + (d.getD 0).den) 0
      if cs = 4242424242424242 then IO.eprintln "randverify: checksum" else pure ()
      let c1 ← IO.monoNanosNow
      let msCheck := ((c1 - c0 : ℕ).toFloat) / 1000000.0
      -- the distances of a finished run, and what they say
      let tail := [flags, ("windows", Lean.toJson n), ("time_ms", Lean.toJson (msReach + msCheck)),
        ("time_check_ms", Lean.toJson msCheck)] ++ shared ++
        [("distances", Json.arr (ds.map aux_sepJson)),
        ("distances_unrounded", Json.arr (du.map aux_sepJson)),
        ("unverifiable_from_rounding", Json.arr ((ds.zip du).map fun (d, u) =>
          Json.bool (aux_sepPos u && !aux_sepPos d))),
        ("verified_hull", Json.bool (!dh.isEmpty && dh.all fun d => d.any (0 < ·))),
        ("distances_hull", Json.arr (dh.map aux_optRat)),
        ("distances_hull_unrounded", Json.arr (dhu.map aux_optRat))]
      if ds.isEmpty || ds.any Option.isNone then
        return finish I "none" "no window or no unsafe box to measure" Json.null tail
      return finish I "ok" "" (Json.bool (ds.all aux_sepPos)) tail

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
