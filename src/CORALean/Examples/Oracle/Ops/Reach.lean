import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.Examples.Oracle.Dtype
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

/-!
# `"linearSysReach"`, via `LinearSys.reachFloat`

`A` is read square and dynamic, `X0` at the dimension `A` fixes; `X0` and the
exact `tFinal` are `reachFloat`'s `params` (`tStart = 0`), `timeStep`,
`taylorTerms` and `zonotopeOrder` its `options`, same names. `LinearSys` here
carries no input (`LinearSys.lean`'s own docstring), so `B`/`U` have nothing to
enter through -- rejected unless every entry is exactly zero, `aux_checkNoInput`.

`timeStep`/`tFinal` are read as arbitrary exact reals: `exactDiv` checks that
`tFinal / timeStep` is a nonnegative integer, cross-multiplied, before either is
asked to fit `𝕋`, so an inexact ratio is refused by name, not for a grid. It is
the check `reachFloat` makes itself, `Reach.steps`, done first for its message.
`timeStep` is then read into `𝕋` exactly, since it is `reachFloat`'s own `Δt`:
refused by name if it does not fit, since rounding it would run a different
time grid than the one asked for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Bench
open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `U`/`B`, if present, must be exactly zero: `LinearSys` has no input term. -/
def aux_checkNoInput (req : Json) : Except String Unit := do
  match fieldOpt req "U" with
  | some uj =>
    let dz ← parseZonotopeScalar uj
    let isZero := dz.h = 0 && dz.c.all ExactScalar.isZero && dz.Einf.all ExactScalar.isZero
      && dz.Esup.all ExactScalar.isZero
    if !isZero then
      throw "linearSysReach: not supported: reachFloat has no input term (`U` is nonzero)"
  | none => pure ()
  match fieldOpt req "B" with
  | some bj =>
    let dm ← parseMatScalarDyn bj
    if !(dm.data.all ExactScalar.isZero) then
      throw "linearSysReach: not supported: reachFloat has no input term (`B` is nonzero)"
  | none => pure ()

/-- `v`, as an exact `(num, den)` fraction, `den > 0` -- `.dy`'s own power of two, or
`.decNeg`'s power of ten. -/
def aux_toRat : ExactScalar → Int × Int
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  | .decNeg m d => (m, 10 ^ d)

/-- `tFinal / timeStep` as a nonnegative integer, exact: both read as `(num, den)` fractions
(`aux_toRat`, binary or decimal alike), cross-multiplied, then integer division checked to
leave no remainder. -/
def exactDiv (tFinal timeStep : ExactScalar) : Except String Nat := do
  let (n1, d1) := aux_toRat tFinal
  let (n2, d2) := aux_toRat timeStep
  if n2 ≤ 0 then throw "linearSysReach: `timeStep` must be positive"
  let num := n1 * d2
  let den := n2 * d1
  if num % den ≠ 0 ∨ num / den < 0 then
    throw s!"linearSysReach: tFinal/timeStep = {showScalarForMessage tFinal}/\
      {showScalarForMessage timeStep} is not a nonnegative integer"
  else pure (num / den).toNat


-- =====================================  MAIN DEFINITION  ====================================== --

def handleLinearSysReach {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (dops : DtypeOps 𝕋) (req : Json) : Except String (List (String × Json)) := do
  aux_checkNoInput req
  let dmA ← parseMatDyn dops.readExact (← field req "A")
  if h : dmA.r = dmA.c then
    let A : Mat 𝕋 dmA.r dmA.r := h ▸ dmA.M
    let n := dmA.r
    let X0 ← parseZonotopeFixed dops.readExact n (← field req "X0")
    let timeStep ← scalarField req "timeStep"
    let tFinal ← scalarField req "tFinal"
    -- refused by name before the run would refuse it with `none`: the same exact division
    let _ ← exactDiv tFinal timeStep
    let Δt ← match dops.readExact "timeStep" timeStep with
      | .ok v => pure v
      | .error _ => throw s!"linearSysReach: timeStep {showScalarForMessage timeStep} is not \
        exactly representable in {dops.label}; reachFloat's time grid would change"
    let eta ← natField req "taylorTerms"
    let rho ← natField req "zonotopeOrder"
    -- CORA's `params` and `options`, under CORA's own names
    let params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ :=
      { X₀ := X0, tFinal := (aux_toRat tFinal).1 / (aux_toRat tFinal).2 }
    let options : LinearSys.ReachOptions 𝕋 :=
      { Δt := Δt, η := eta, ρ := rho }
    match LinearSys.reachFloat (𝕋 := 𝕋) (LinearSys.canonicalFloat A) params options with
    | none => throw s!"linearSysReach: reachFloat returned none -- no admissible Taylor order \
        (raised from taylorTerms = {eta}) was found for this timeStep"
    | some (Rti, Rtp) =>
      pure
        [ ("timePoint", Json.arr (Rtp.toArray.map (printZonotope dops.showExact))),
          ("timeInterval", Json.arr (Rti.toArray.map (printZonotope dops.showExact))) ]
  else throw s!"linearSysReach: `A` must be square, not {dmA.r}×{dmA.c}"

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
