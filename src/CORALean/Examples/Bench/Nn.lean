import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Bench.NearestUnsound.Instances
import CORALean.Examples.Bench.NnNetwork
import CORALean.Examples.Bench.Timing
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NnNaive
import CORALean.Examples.Bench.Rational
import CORALean.Global.Float.Instances.Binary64.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.IEEE.Instances
import CORALean.NN.Operations.Enclose
import CORALean.Specification.Instances
import CORALean.Specification.Operations.Check
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Basic
import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# `lake exe bench nn-float32 [--reps N] [--out DIR]`

Naive binary32 verification certifies `y ≤ 0` for `NnNetwork`'s network; the real
network the weights denote violates it at `xStar`; CORALean's enclosure, sound at
`IEEE binary32`, `IEEE binary64`, `Dyadic 24` and `Float`, does not certify it. Ten
analyses, each timed over `--reps` runs (default `5`): naive IBP and naive zonotopes
in round-to-nearest `Float32`, and `NeuralNetwork.enclose` over float intervals and
float zonotopes at the four sound scalars. Two more run that same `enclose` at `NearestDyadic 24`,
round-to-nearest binary32 as CORA would: the paper's baseline, with NO guarantee.
`--type`/`--format`/`--prec`/`--config` are ignored.

Writes `<out>/nn/nn-float32.json` -- the network, `X`, the property, `xStar`, the
exact and binary32 outputs there, each analysis's bounds, verdict and timings, and
the git and machine info `GitInfo` collects -- and prints the same as a table.
Every number is reported exactly, as `"m/2^k"`, beside its nearest double.

The analyses' inputs are read back through an `IO.Ref` inside the timed window, so
the compiler cannot hoist a closed analysis out of the loop and time nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)
open scoped Matrix

/-- `d` with its mantissa odd (or `0/2^0`), so equal numbers print equally. -/
def ExactDyadic.normalize (d : ExactDyadic) : ExactDyadic :=
  if d.mantissa = 0 then ExactDyadic.zero else
  let (odd, k) := stripTwos d.mantissa.natAbs
  ⟨if d.mantissa < 0 then -(odd : Int) else (odd : Int), d.exponent + k⟩

/-- `"m/2^k"`, `k ≥ 0` and as small as it can be: `"1/2^2"`, `"16777216/2^0"`. -/
def ExactDyadic.frac (d : ExactDyadic) : String :=
  let d := d.normalize
  if 0 ≤ d.exponent then s!"{d.mantissa * 2 ^ d.exponent.toNat}/2^0"
  else s!"{d.mantissa}/2^{(-d.exponent).toNat}"

def ExactDyadic.le (x y : ExactDyadic) : Bool := (x.add y.neg).mantissa ≤ 0

/-- `d` as an exact decimal JSON number, `m/2^k = m·5^k/10^k`: every digit, so a
double read back from it is exactly the double `d` is (every value here is one). -/
def ExactDyadic.toJsonNumber (d : ExactDyadic) : Lean.JsonNumber :=
  let d := d.normalize
  if 0 ≤ d.exponent then ⟨d.mantissa * 2 ^ d.exponent.toNat, 0⟩
  else ⟨d.mantissa * 5 ^ (-d.exponent).toNat, (-d.exponent).toNat⟩

/-- `d` to ten decimal places, rounded up if `up` and down otherwise, so a printed
enclosure still encloses; exact for every `d` with `k ≤ 10`. -/
def ExactDyadic.decimal (d : ExactDyadic) (up : Bool) : String :=
  let d := d.normalize
  if 0 ≤ d.exponent then toString (d.mantissa * 2 ^ d.exponent.toNat) else
  let den : Int := 2 ^ (-d.exponent).toNat
  let num := d.mantissa * 10 ^ 10
  toString (Lean.JsonNumber.mk (if up then -((-num).fdiv den) else num.fdiv den) 10)

namespace Nn

def ofFloat (x : Float) : ExactDyadic :=
  let d := Binary64.toDyadic x
  ⟨d.mantissa, d.exponent⟩

/-- Exact: every binary32 value is a binary64 value. -/
def ofFloat32 (x : Float32) : ExactDyadic := ofFloat x.toFloat

def ofDyadic {p : ℕ} (x : Dyadic p) : ExactDyadic := ⟨x.mantissa, x.exponent⟩

/-- A number as JSON: `"m/2^k"`, and the double it is, every decimal digit written. -/
def numJson (d : ExactDyadic) : Json :=
  Json.mkObj [("exact", Json.str d.frac), ("double", Json.num d.toJsonNumber)]

def layerJson (L : Layer ExactDyadic) (activation : String) : Json :=
  Json.mkObj
    [ ("W", Json.arr (L.W.map fun row => Json.arr (row.map numJson))),
      ("b", Json.arr (L.b.map numJson)),
      ("activation", Json.str activation) ]

/-- One analysis's answer: the bounds on `y` it computed, exact, and whether they
certify `y ≤ threshold`; `E` is a float zonotope's error box, already in the bounds. -/
structure Outcome where
  method : String
  arithmetic : String
  sound : Bool
  lo : ExactDyadic
  hi : ExactDyadic
  E : Option (ExactDyadic × ExactDyadic)
  certifies : Bool
  samples : Array Nat
  medianNs : Nat

/-- One entry of the JSON's `analyses`. -/
def Outcome.json (o : Outcome) : Json :=
  Json.mkObj
    [ ("method", Json.str o.method),
      ("arithmetic", Json.str o.arithmetic),
      ("sound", Json.bool o.sound),
      ("y_lower", numJson o.lo),
      ("y_upper", numJson o.hi),
      ("error_box", match o.E with
        | some (l, u) => Json.mkObj [("inf", numJson l), ("sup", numJson u)]
        | none => Json.null),
      ("certifies", Json.bool o.certifies),
      ("timingsNs", Json.arr (o.samples.map Lean.toJson)),
      ("medianNs", Lean.toJson o.medianNs) ]

/-- Runs `run` on `x` `reps` times, timing each. `x` is read back from an `IO.Ref`
inside the window, and `force`'s sum of every result decides a branch before the clock
stops -- a `Float` sum, as `Timing.lean` explains, since `&&` would short-circuit. -/
def timeReps {α β : Type} (reps : ℕ) (x : β) (run : β → α) (force : α → Float) :
    IO (Array Nat × Nat × Option α) := do
  let ref ← IO.mkRef x
  let mut samples := #[]
  let mut last := none
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r := run (← ref.get)
    if (force r).isNaN then IO.eprintln "nn-float32: a bound is NaN" else pure ()
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
    last := some r
  pure (samples, medianNanos samples, last)

/-- Both naive binary32 analyses, their bounds read off the box they return. -/
def naive (reps : ℕ) (method : String) (run : Box32 → Box32) (X : Box32) : IO Outcome := do
  let (samples, med, r) ← timeReps reps X run fun B =>
    (B.lo.getD 0 0).toFloat + (B.hi.getD 0 0).toFloat
  let B := r.getD X
  let lo := ofFloat32 (B.lo.getD 0 0)
  let hi := ofFloat32 (B.hi.getD 0 0)
  pure ⟨method, "binary32, round to nearest", false, lo, hi, none,
    hi.le threshold, samples, med⟩

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `NeuralNetwork.enclose` over float zonotopes at `𝕋`, and `Specification.check`
on what comes back. -/
def soundZonotope (inst : ExactDyadic → 𝕋) : Zonotope (Vec 𝕋 1) × Bool :=
  let Z := (network (S := 𝒵[𝕋]) (layer₁.mat inst 1 1) (layer₁.vec inst 1)
    (layer₂.mat inst 1 1) (layer₂.vec inst 1)).enclose (inputZonotope inst)
  (Z, (spec inst).check Z)

/-- What its bounds are worth, at binary32's precision: the exact network at
every point of `X` lies in the enclosure `soundZonotope` computes. -/
example {x : Vec ℝ 1}
    (hx : x ∈ ContSet.construct (inputZonotope (𝕋 := Dyadic 24) ExactDyadic.toDyadicPUnchecked)) :
    let inst : ExactDyadic → Dyadic 24 := ExactDyadic.toDyadicPUnchecked
    Scalar.toRealMat (layer₂.mat inst 1 1) *ᵥ (fun i => Real.relu ((Scalar.toRealMat
        (layer₁.mat inst 1 1) *ᵥ x + Scalar.toRealVec (layer₁.vec inst 1)) i))
      + Scalar.toRealVec (layer₂.vec inst 1) ∈ ContSet.construct (soundZonotope inst).1 :=
  network_mem_enclose _ _ _ _ _ hx

/-- The same over float intervals. -/
def soundInterval (inst : ExactDyadic → 𝕋) : Interval (Vec 𝕋 1) × Bool :=
  let I := (network (S := ℐ𝒱[𝕋]) (layer₁.mat inst 1 1)
    (layer₁.vec inst 1) (layer₂.mat inst 1 1) (layer₂.vec inst 1)).enclose (inputBox inst)
  (I, (spec inst).check I)

/-- Both sound analyses at `𝕋`, the zonotope's bounds its interval hull (error box
included), each forced through its hull and its verdict. -/
def sound (reps : ℕ) (arithmetic : String) (inst : ExactDyadic → 𝕋) (toD : 𝕋 → Float)
    (toExact : 𝕋 → ExactDyadic) : IO (Outcome × Outcome) := do
  let bit (ok : Bool) : Float := if ok then 1 else 0
  let (sI, mI, rI) ← timeReps reps inst soundInterval fun (I, ok) =>
    toD (I.inf 0) + toD (I.sup 0) + bit ok
  let (sZ, mZ, rZ) ← timeReps reps inst soundZonotope fun (Z, ok) =>
    toD (Z.interval.inf 0) + toD (Z.interval.sup 0) + bit ok
  let (I, okI) := rI.getD (soundInterval inst)
  let (Z, okZ) := rZ.getD (soundZonotope inst)
  let H := Z.interval
  pure (⟨"interval", arithmetic, true, toExact (I.inf 0), toExact (I.sup 0), none, okI, sI, mI⟩,
    ⟨"zonotope", arithmetic, true, toExact (H.inf 0), toExact (H.sup 0),
      some (toExact (Z.I_error.inf 0), toExact (Z.I_error.sup 0)), okZ, sZ, mZ⟩)

open CORALean.Bench.NearestUnsound in
/-- `sound`'s two analyses at `NearestDyadic 24`, round-to-nearest binary32 — the
same `enclose`, unverified — and so reported unsound. -/
def nearest (reps : ℕ) : IO (Outcome × Outcome) := do
  let (I, Z) ← sound (𝕋 := NearestDyadic 24) reps "round-to-nearest binary32 (unverified)"
    (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) (fun x => dyadicToFloatApprox x.val)
    (fun x => ofDyadic x.val)
  pure ({ I with sound := false }, { Z with sound := false })

/-- `s` padded with spaces to `w` characters. -/
def pad (w : ℕ) (s : String) : String := s.pushn ' ' (w - s.length)

def row (o : Outcome) : String :=
  pad 10 o.method ++ pad 40 o.arithmetic ++ pad 7 (if o.sound then "yes" else "no")
    ++ pad 30 s!"[{o.lo.decimal false}, {o.hi.decimal true}]"
    ++ pad 11 (if o.certifies then "YES" else "no") ++ s!"{o.medianNs}"

end Nn

open Nn


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Checks the data fits binary32, runs the twelve analyses and both point
evaluations, prints the table and writes `<out>/nn/nn-float32.json`. -/
def runNnFloat32 (args : CliArgs) : IO Unit := do
  let reps := args.reps.getD 5
  let data := (layer₁.W.flatten ++ layer₁.b ++ layer₂.W.flatten ++ layer₂.b ++ boxLo ++ boxHi
    ++ xStar).push threshold
  if !data.all (fitsPrecision 24) then
    throw (IO.userError "nn-float32: a weight, bound or input needs more than 24 bits")
  -- the network at `xStar`, exactly and as deployed in binary32
  let yExact := (pointEval exactArith layer₁ layer₂ xStar).getD 0 ExactDyadic.zero
  let yF32 := ofFloat32 ((pointEval f32Arith (layer₁.map ExactDyadic.toFloat32)
    (layer₂.map ExactDyadic.toFloat32) (xStar.map ExactDyadic.toFloat32)).getD 0 0)
  let L₁ := layer₁.map ExactDyadic.toFloat32
  let L₂ := layer₂.map ExactDyadic.toFloat32
  let X : Box32 := ⟨boxLo.map ExactDyadic.toFloat32, boxHi.map ExactDyadic.toFloat32⟩
  -- the analyses: naive binary32, then sound at `Dyadic 24`, `Float` and the two formats
  let ibpO ← naive reps "interval" (ibp L₁ L₂) X
  -- the naive zonotope's input: `X`'s center and radius, both exact in binary32
  let zonoO ← naive reps "zonotope" (fun B => Zono32.box (zono L₁ L₂
    ⟨Array.zipWith (fun l u => (l + u) / 2) B.lo B.hi,
      #[Array.zipWith (fun l u => (u - l) / 2) B.lo B.hi]⟩)) X
  let (d24I, d24Z) ← sound (𝕋 := Dyadic 24) reps "Dyadic 24, outward rounding"
    ExactDyadic.toDyadicPUnchecked dyadicToFloatApprox ofDyadic
  let (f64I, f64Z) ← sound (𝕋 := Float) reps "binary64 (Float), outward rounding"
    ExactDyadic.toFloatUnchecked id ofFloat
  -- the formats themselves, subnormals and all; every input here is a binary32 number
  let (i32I, i32Z) ← sound (𝕋 := IEEE .binary32) reps "IEEE binary32, outward rounding"
    ExactDyadic.toIEEEUnchecked ieeeToFloatApprox fun x => ⟨x.mantissa, x.exponent⟩
  let (i64I, i64Z) ← sound (𝕋 := IEEE .binary64) reps "IEEE binary64, outward rounding"
    ExactDyadic.toIEEEUnchecked ieeeToFloatApprox fun x => ⟨x.mantissa, x.exponent⟩
  -- the unsound baseline: the same `enclose`, rounding to nearest as CORA does
  let (nI, nZ) ← nearest reps
  let outcomes := #[ibpO, zonoO, d24I, d24Z, f64I, f64Z, nI, nZ, i32I, i32Z, i64I, i64Z]
  -- the table: the example, then one row per analysis
  let first (a : Array ExactDyadic) : String := (a.getD 0 ExactDyadic.zero).decimal false
  IO.println s!"nn-float32: y = relu(x + 2^24) - 2^24 on X = [{first boxLo}, {first boxHi}], \
    property y <= {threshold.decimal false}"
  IO.println s!"  x* = {first xStar}: exact y = {yExact.decimal false}, \
    binary32 y = {yF32.decimal false}"
  IO.println (pad 10 "method" ++ pad 40 "arithmetic" ++ pad 7 "sound" ++ pad 30 "y in"
    ++ pad 11 "certifies" ++ "median ns")
  for o in outcomes do IO.println (row o)
  -- the same, and everything else a reader needs to rerun it, as JSON
  let dir := System.FilePath.mk args.outDir / "nn"
  IO.FS.createDirAll dir
  let mach ← machineInfo
  let doc := Json.mkObj
    [ ("experiment", Json.str "nn-float32"),
      ("network", Json.mkObj
        [ ("formula", Json.str "y = relu(x + 2^24) - 2^24"),
          ("layers", Json.arr #[layerJson layer₁ "relu", layerJson layer₂ "none"]) ]),
      ("input_box", Json.mkObj
        [("lo", Json.arr (boxLo.map numJson)), ("hi", Json.arr (boxHi.map numJson))]),
      ("property", Json.mkObj
        [("formula", Json.str s!"y <= {threshold.frac}"), ("threshold", numJson threshold)]),
      -- the counterexample, and the network there exactly and in binary32
      ("x_star", Json.arr (xStar.map numJson)),
      ("y_exact", numJson yExact),
      ("y_binary32", numJson yF32),
      ("violated_exact", Json.bool !(yExact.le threshold)),
      ("violated_binary32", Json.bool !(yF32.le threshold)),
      ("analyses", Json.arr (outcomes.map Outcome.json)),
      -- what the run ran on
      ("reps", Lean.toJson reps),
      ("gitCommit", Json.str (← gitCommit)),
      ("leanVersion", Json.str (← leanVersion)),
      ("machine", Json.mkObj
        [ ("uname", Json.str mach.uname), ("cpu", Json.str mach.cpu),
          ("cores", Lean.toJson mach.cores) ]) ]
  let out := dir / "nn-float32.json"
  IO.FS.writeFile out doc.pretty
  IO.println s!"nn-float32: wrote {out}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
