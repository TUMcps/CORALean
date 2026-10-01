import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatOuter
import CORALean.Examples.Bench.FirstStepHead
import CORALean.Examples.Bench.FirstStepPrec
import CORALean.Examples.Bench.RandVerifyRun
import CORALean.Examples.Bench.RandVerifyTypes
import CORALean.Examples.Bench.Registry
import CORALean.Global.Float.Instances.Flint.API

/-!
# `bench-flint`'s logic: parsing, dispatch, self-test, positive control

The bulk of `bench-flint` (README, "FLINT backend (optional)"); `main` lives in
`Examples/BenchFlintMain.lean`, so `check-axioms.lean` can import this file's
`reachFloat_outer_flint` beside `Examples/Bench.lean` without two `main`s.

`dispatchFlint` reuses `parseArgs` for every flag but `--type`, accepted only
as `flint`, and `Registry.lean`'s `runAt` to run `args.experiment` at
`Flint (resolvedPrec args)`, as `dispatch` runs it at `Dyadic p`.

`bench-flint firststep` makes `firststep`'s `flint` runs, `bench` the rest.
`bench-flint selftest` differential-tests instead: for `p` in `{2, 11, 24, 53,
113}` and pseudo-random pairs (fixed seed, negative and past `2^64`, to reach
the FFI's big-`Int` path), it compares `Flint p`'s six rounded operations
against `Dyadic p`'s by exact value, not representation -- FLINT normalises
the mantissa odd, `Dyadic` need not. `reachFloat_outer_flint` is
`check-axioms.sh`'s positive control for `trustedFlint`, the one axiom this
file and the `Flint` instances may reach.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

/-- `argv` with `--type flint` dropped; an error if `--type` names anything
else, since this exe only ever runs `Flint`. Not `aux_`: `main`, in
`Examples/BenchFlintMain.lean`, calls it. -/
def stripTypeFlint : List String → Except String (List String)
  | [] => pure []
  | "--type" :: v :: rest => do
    if v ≠ "flint" then throw s!"bench-flint only supports `--type flint`, not `{v}`"
    stripTypeFlint rest
  | x :: rest => do
    let rest' ← stripTypeFlint rest
    pure (x :: rest')


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step of a splitmix64 generator (Steele/Lea/Flood), for a
reproducible, dependency-free fixed seed. -/
def aux_splitmix64 (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z := s'
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  let z := z ^^^ (z >>> 31)
  (z, s')

/-- A pseudo-random mantissa: small, `UInt64`-sized, or past `2^64` (the
FFI's big-`Int` path), signed by a further bit. -/
def aux_randMantissa (s : UInt64) : Int × UInt64 :=
  let (cls, s1) := aux_splitmix64 s
  let (hi, s2) := aux_splitmix64 s1
  let (lo, s3) := aux_splitmix64 s2
  let mag : Int :=
    match cls.toNat % 4 with
    | 0 => ((hi.toNat % (2 ^ 20 : Nat) : Nat) : Int)
    | 1 => (hi.toNat : Int)
    | 2 => (hi.toNat : Int) * ((2 : Int) ^ (64 : Nat)) + (lo.toNat : Int)
    | _ => 0
  (if lo % 2 = 1 then -mag else mag, s3)

/-- A pseudo-random exponent in `[-30, 30]`. -/
def aux_randExponent (s : UInt64) : Int × UInt64 :=
  let (r, s') := aux_splitmix64 s
  ((((r.toNat % 61 : Nat) : Int) - 30), s')

/-- `m₁ * 2 ^ e₁ = m₂ * 2 ^ e₂` decided exactly by aligning to the smaller
exponent -- results may use different mantissas for the same value. -/
def aux_dyadicValueEq (m1 e1 m2 e2 : Int) : Bool :=
  let e := min e1 e2
  m1 * (2 : Int) ^ (e1 - e).toNat == m2 * (2 : Int) ^ (e2 - e).toNat

/-- The six directed operations, `Flint p` paired with `Dyadic p`, named for
a mismatch report. -/
def aux_selftestOps (p : ℕ) :
    List (String × (Flint p → Flint p → Flint p) × (Dyadic p → Dyadic p → Dyadic p)) :=
  [("addUp", Flint.addUp p, Dyadic.addUp), ("addDown", Flint.addDown p, Dyadic.addDown),
   ("mulUp", Flint.mulUp p, Dyadic.mulUp), ("mulDown", Flint.mulDown p, Dyadic.mulDown),
   ("divUp", Flint.divUp p, Dyadic.divUp), ("divDown", Flint.divDown p, Dyadic.divDown)]

/-- `trials` random pairs at precision `p`: every op run at both scalars and
compared by exact value, the divisor forced nonzero. Prints mismatches,
returns (compared, mismatched). -/
def aux_selftestAtPrec (p : ℕ) (trials : ℕ) (seed0 : UInt64) : IO (ℕ × ℕ) := do
  let mut s := seed0
  let mut tested := 0
  let mut mismatches := 0
  for _ in [0:trials] do
    -- one operand pair, the divisor's mantissa nudged off zero
    let (m1, s1) := aux_randMantissa s
    let (e1, s2) := aux_randExponent s1
    let (m2raw, s3) := aux_randMantissa s2
    let (e2, s4) := aux_randExponent s3
    let m2 := if m2raw = 0 then 1 else m2raw
    s := s4
    let a : Flint p := ⟨m1, e1⟩
    let b : Flint p := ⟨m2, e2⟩
    let aD : Dyadic p := ⟨m1, e1⟩
    let bD : Dyadic p := ⟨m2, e2⟩
    -- every directed op at this one pair, `Flint` against `Dyadic`
    for (name, fF, fD) in aux_selftestOps p do
      let rF := fF a b
      let rD := fD aD bD
      tested := tested + 1
      if !aux_dyadicValueEq rF.mantissa rF.exponent rD.mantissa rD.exponent then
        mismatches := mismatches + 1
        IO.eprintln s!"MISMATCH p={p} {name} a=({m1},{e1}) b=({m2},{e2}) \
          flint=({rF.mantissa},{rF.exponent}) dyadic=({rD.mantissa},{rD.exponent})"
  pure (tested, mismatches)

/-- `bench-flint selftest`: `{2, 11, 24, 53, 113}`, `3000` pairs each, a
fixed seed. Exits nonzero on any mismatch. -/
def aux_runSelftest : IO Unit := do
  let ps : List ℕ := [2, 11, 24, 53, 113]
  let mut totalTested := 0
  let mut totalMismatch := 0
  for p in ps do
    let (tested, mism) ← aux_selftestAtPrec p 3000 (0x243F6A8885A308D3 + p.toUInt64)
    IO.println s!"selftest p={p}: {tested} comparisons, {mism} mismatches"
    totalTested := totalTested + tested
    totalMismatch := totalMismatch + mism
  IO.println s!"selftest: {totalTested} total comparisons, {totalMismatch} mismatches"
  if totalMismatch > 0 then IO.Process.exit 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `firststep`'s `flint` records, `Flint p` at the same `p` as `Dyadic p`; `none` for any other
type, which `bench` makes. -/
def aux_firstStepFlint (cfg : HeadlineConfig) (run : FirstStepRun) (dt : String) :
    Option Json :=
  if run.ty ≠ "flint" then none else
  -- `Flint p` at the width `Dyadic p` has, read as `Dyadic.toDyadicP` reads a config leaf
  let p := run.sigBits
  let nt : NumberType (Flint p) :=
    { description := s!"flint {dyadicDescription (precToFormat p) p}" }
  some (firstStepRecord cfg (firstStepHead "flint" s!"p{p}" p nt)
    (fun field d => if fitsPrecision p d then pure ⟨d.mantissa, d.exponent⟩
      else throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more than {p} bits")
    (fun d => ⟨d.mantissa, d.exponent⟩) nt dt)

/-- `randverify`'s `flint<p>` types, `Flint p` read as `aux_firstStepFlint` reads it; `none` for
any other label, which `bench` runs. -/
def aux_randVerifyFlint (label : String) (J : RandJob) : Option (IO Json) :=
  match randTypeKind label with
  | some ("flint", some p) =>
    let nt : NumberType (Flint p) :=
      { description := s!"flint {dyadicDescription (precToFormat p) p}" }
    some (randVerifyRecord (firstStepHead "flint" s!"p{p}" p nt) nt
      (fun field d => if fitsPrecision p d then pure ⟨d.mantissa, d.exponent⟩
        else throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more \
          than {p} bits")
      (fun d => ⟨d.mantissa, d.exponent⟩) J)
  | _ => none

/-- `args.experiment` run at `Flint (resolvedPrec args)`, through `runAt` --
`inst`/`instUnchecked`/`toD` mirror `Dyadic`'s in `Registry.lean`. -/
def dispatchFlint (args : CliArgs) : IO Unit :=
  if args.experiment = "selftest" then aux_runSelftest else
  if args.experiment = "firststep" then
    runFirstStepWith args "results-flint" aux_firstStepFlint else
  if args.experiment = "randverify" then
    runRandVerifyWith args "-flint" aux_randVerifyFlint else
  let p := resolvedPrec args
  let inst : String → ExactDyadic → Except String (Flint p) := fun field d =>
    if fitsPrecision p d then pure ⟨d.mantissa, d.exponent⟩
    else throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more than {p} bits"
  let instUnchecked : ExactDyadic → Flint p := fun d => ⟨d.mantissa, d.exponent⟩
  let toD : Flint p → Float := fun x => dyadicToFloatApprox x.toDyadic
  let toExact : Option (Flint p → String) :=
    if args.exact then some (fun x => s!"{x.mantissa}*2^{x.exponent}") else none
  runAt (𝕋 := Flint p) args inst instUnchecked toD (precToFormat p) toExact p

/-- `reachFloat_outer` at `Flint 53`: `check-axioms.sh`'s positive control
for `trustedFlint`. Never a use site of its own. -/
theorem reachFloat_outer_flint :
    type_of% (@LinearSys.reachFloat_outer (Flint 53) _ _ _ 2) :=
  @LinearSys.reachFloat_outer (Flint 53) _ _ _ 2

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
