import CORALean.Examples.Bench.Rollout

/-!
# Timing a rollout, forced and repeated

`IO.monoNanosNow` around the call, `reps` times, the array's median reported
alongside every raw sample. `checksum` is folded over the result *inside* that
window and its outcome is what decides a branch before the clock stops --
without that, the interpreter defers the actual arithmetic past `t1`, and the
measured sample is a handful of nanoseconds while the real cost turns up later
inside `writeRun`, once serialising the output is what finally demands every
generator. Confirmed by wrapping the whole call in an outer, coarser timer and
watching it disagree with the sum of the "measured" per-rep samples by orders
of magnitude until the checksum's result was genuinely forced.

The forcing itself has to differ by branch: `if cs == cs then pure () else
pure ()` looks like it demands `cs` and does not, since both branches reduce
to the same `pure ()` and the compiler drops the condition. `cs.isNaN`
in a branch that only sometimes prints is what actually has to be decided. -/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The sum of every `Float` a zonotope's four fields hold, over a whole
rollout -- forces every entry of every step, so the loop the array came from
cannot have left anything unevaluated. -/
def checksum (toD : 𝕋 → Float) (arr : Array (Zonotope (Vec 𝕋 2))) : Float :=
  arr.foldl (fun acc Z =>
    let cSum := (Array.ofFn Z.c).foldl (· + toD ·) 0.0
    let rowSum (i : Fin 2) : Float := (Array.ofFn fun j => Z.G j i).foldl (· + toD ·) 0.0
    let gSum := (Array.ofFn rowSum).foldl (· + ·) 0.0
    let iSum := (Array.ofFn Z.E.inf).foldl (· + toD ·) 0.0
    let sSum := (Array.ofFn Z.E.sup).foldl (· + toD ·) 0.0
    acc + cSum + gSum + iSum + sSum) 0.0

/-- The middle sample once `xs` is sorted -- `reps` is always small and odd in
practice, and an even count just picks the upper of the two middle samples,
which is not worth a second case for a number that is never load-bearing. -/
def medianNanos (xs : Array Nat) : Nat :=
  let sorted := xs.qsort (· < ·)
  sorted.getD (sorted.size / 2) 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Runs `rollout` `reps` times, timing each with `IO.monoNanosNow` and forcing
the result through `checksum`. Returns every sample in nanoseconds, their
median, and the last run's checksum and array (every run computes the same). -/
def timeRollout (toD : 𝕋 → Float) (S : System 𝕋) (o N reps : ℕ) :
    IO (Array Nat × Nat × Float × Array (Zonotope (Vec 𝕋 2))) := do
  let mut samples := #[]
  let mut lastArr := #[]
  let mut lastSum := 0.0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let arr := rollout S o N
    let cs := checksum toD arr
    -- forces `cs`, and with it every entry `checksum` folded over -- see the module docstring
    if cs.isNaN then
      IO.eprintln "bench: checksum is NaN -- a step likely overflowed at this precision"
    else pure ()
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
    lastArr := arr
    lastSum := cs
  pure (samples, medianNanos samples, lastSum, lastArr)

/-- Runs `f ()` -- a `headline-a`/`headline-b`/`exp2-timepoint` algorithm call
-- `reps` times, forcing a `some` result's lists through `checksum` exactly as
`timeRollout` forces `rollout`'s; a `none` needs no forcing. -/
def timeAlgo (toD : 𝕋 → Float)
    (f : Unit → Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2)))) (reps : ℕ) :
    IO (Array Nat × Nat × Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2)))) := do
  let mut samples := #[]
  let mut lastR : Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2))) := none
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r := f ()
    match r with
    | none => pure ()
    | some (ti, tp) =>
      let cs := checksum toD ti.toArray + checksum toD tp.toArray
      if cs.isNaN then
        IO.eprintln "bench: checksum is NaN -- a step likely overflowed at this precision"
      else pure ()
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
    lastR := r
  pure (samples, medianNanos samples, lastR)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
