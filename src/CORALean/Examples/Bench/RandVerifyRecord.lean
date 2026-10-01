import CORALean.Examples.Bench.FirstStepJson
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.RandVerifyDistance
import CORALean.Examples.Bench.RandVerifyHull
import CORALean.Examples.Bench.RandVerifyJob
import CORALean.Examples.Bench.RandVerifyNumber
import CORALean.Examples.Bench.RandVerifyRead
import CORALean.Examples.Bench.RandVerifyReach
import CORALean.Examples.Bench.RandVerifyUnsafe

/-!
# `randverify`: one instance, one number type, one algorithm

The system is read exactly (`readRandSystem`; a format that cannot hold it is `"none"`, never a
rounded system), the unsafe boxes are rounded outward, the windows of `randVerifyReach` are
mapped to output space and hulled, and each unsafe box gets its signed distance (positive when
every window is separated, in exact rationals). The record's `status` is `"ok"`, `"none"` with
a `reason`, or `"overflow-NaN"`, a bound or hull past the format's range or `NaN`, which gives no
distance and `verified: false`. `verified` is `true` iff every distance is positive, `null` where
there is nothing to say (`none`). `distances_unrounded` is the same against the file's own
unsafe boxes, and `unverifiable_from_rounding[j]` says it is positive there and not here: the
outward rounding alone cost the proof. `time_ms` is the wall clock of reach, hull and distances.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
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

/-- The `params` the record echoes. -/
def aux_paramsJson (J : RandJob) : Json :=
  Json.mkObj [("dt", Json.str J.dt), ("eta", Lean.toJson J.eta), ("order", Lean.toJson J.rho),
    ("tend", ratJson J.inst.tend)]

/-- Windows, overflow flag, distances against the rounded and the file's own unsafe boxes. -/
def aux_compute (nonFinite : 𝕋 → Bool) (J : RandJob) (S : RandSystem 𝕋)
    (uns : Array (Array (𝕋 × 𝕋 × Bool × Bool))) :
    Except String (ℕ × Bool × Array (Option ℚ) × Array (Option ℚ)) := do
  let Rs ← randVerifyReach J.alg S J.inst.tend J.eta J.rho
  let hulls := outputHulls S.C Rs
  let bad := hulls.any fun H =>
    (List.finRange 2).any fun i => nonFinite (H.inf i) || nonFinite (H.sup i)
  -- an infinite or `NaN` hull has no distance
  if bad then pure (Rs.length, true, #[], #[]) else
  -- the hulls as exact rationals, one `(inf, sup)` per output dimension
  let hq := hulls.map fun H =>
    Array.ofFn fun i : Fin 2 => (ToRat.toRat (H.inf i), ToRat.toRat (H.sup i))
  pure (Rs.length, false,
    uns.map fun s => signedDistance hq (s.map fun (l, h, _, _) => (ToRat.toRat l, ToRat.toRat h)),
    J.inst.unsafeSets.map (signedDistance hq))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The record; `head` is `firstStepHead`'s `type`, `format`, `significand_bits`. -/
def randVerifyRecord (head : List (String × Json)) (nt : NumberType 𝕋)
    (inst : String → ExactDyadic → Except String 𝕋) (exactIn : ExactDyadic → 𝕋) (J : RandJob) :
    IO Json := do
  -- what a record that got no distances says
  let nonFinite : 𝕋 → Bool := nt.overflows.getD fun _ => false
  let nulls : List (String × Json) := [("distances", Json.null), ("distances_unrounded", Json.null),
    ("unverifiable_from_rounding", Json.null), ("windows", Json.null), ("time_ms", Json.null)]
  let finish (status reason : String) (verified : Json) (extra : List (String × Json)) : Json :=
    Json.mkObj (head ++ [("instance", Json.str J.inst.name), ("algorithm", Json.str J.alg.name),
      ("status", Json.str status), ("reason", Json.str reason), ("verified", verified)] ++
      extra ++ [("params", aux_paramsJson J)])
  match parseRandString J.dt with
  | .error e => pure (finish "none" s!"dt: {e}" Json.null nulls)
  | .ok dtQ =>
  match readRandSystem inst J.inst dtQ with
  | .error e => pure (finish "none" s!"not representable: {e}" Json.null nulls)
  | .ok S =>
  -- the unsafe boxes, rounded outward into the format
  let uns := J.inst.unsafeSets.map (roundUnsafeOut exactIn)
  let flags := ("unsafe_rounded", Json.arr (uns.map fun s => Json.arr (s.map fun (_, _, a, b) =>
    Json.mkObj [("lb", Json.bool a), ("ub", Json.bool b)])))
  if uns.any (·.any fun (l, h, _, _) => nonFinite l || nonFinite h) then
    pure (finish "overflow-NaN" "an unsafe bound rounds out of the format's range"
      (Json.bool false) (flags :: nulls))
  else
  let t0 ← IO.monoNanosNow
  let res := aux_compute nonFinite J S uns
  -- forces `res` before the clock stops, as `timeAlgo` does
  match res with
  | .ok (_, _, ds, du) =>
    let cs := (ds ++ du).foldl (fun a d => a + d.getD 0) (0 : ℚ)
    if cs = 4242424242424242 then IO.eprintln "randverify: checksum" else pure ()
  | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  -- the record for each way the run can end
  let ms := ((t1 - t0 : ℕ).toFloat) / 1000000.0
  let timeJ := ("time_ms", Lean.toJson ms)
  match res with
  | .error e =>
    pure (finish "none" e Json.null ((flags :: nulls.filter (·.1 ≠ "time_ms")) ++ [timeJ]))
  | .ok (n, true, _, _) =>
    pure (finish "overflow-NaN" "an output hull is past the format's range or NaN"
      (Json.bool false) ([flags, ("windows", Lean.toJson n), timeJ] ++
        nulls.filter (·.1 ∈ ["distances", "distances_unrounded", "unverifiable_from_rounding"])))
  | .ok (n, false, ds, du) =>
    -- the distances of a finished run, and what they say
    let tail := [flags, ("windows", Lean.toJson n), timeJ,
      ("distances", Json.arr (ds.map aux_optRat)),
      ("distances_unrounded", Json.arr (du.map aux_optRat)),
      ("unverifiable_from_rounding", Json.arr ((ds.zip du).map fun (d, u) =>
        Json.bool (u.any (0 < ·) && d.any (· ≤ 0))))]
    if ds.isEmpty || ds.any Option.isNone then
      pure (finish "none" "no window or no unsafe box to measure" Json.null tail)
    else pure (finish "ok" "" (Json.bool (ds.all fun d => d.any (0 < ·))) tail)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
