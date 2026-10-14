import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.Examples.Bench.FirstStepJson
import CORALean.Examples.Bench.FirstStepRat
import CORALean.Examples.Bench.FirstStepRound
import CORALean.Examples.Bench.NumberType
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

/-!
# `firststep`: one number type at one `dt`, one step

The headline spiral `A = [[a, b], [-b, a]]`, the config's `X0` and `eta`, `rho`, run through
`LinearSys.reachFloat` -- `headline-b`'s own call, `Registry.aux_algoHeadlineB` -- with
`tFinal = dt`, so `N = 1`: `Rti = [R_0]`, the first time-interval enclosure, and
`Rtp = [X_0, X_1]`, the time-point sets.

`A` and `dt` are read exactly through `inst`, as `buildContSystem` reads them, and a format that
cannot hold one is a `"none"` record saying `not representable`. `X0` is the exception: it is
rounded outward (`roundX0In`), so a format too coarse for it still has a first step, from the
set it can hold. The record's `status` is `"ok"`; `"overflow-NaN"` if any stored scalar of
`x0`, `R0` or `X1` is past the format's range or a `NaN` (`nt.overflows`), the numbers still
given where they are rational; `"none"` with a `reason` for everything else.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every scalar a zonotope stores. -/
def aux_scalars (Z : Zonotope (Vec 𝕋 2)) : List 𝕋 :=
  List.ofFn Z.c ++ (List.ofFn fun i => List.ofFn fun j => Z.G j i).flatten ++
    List.ofFn Z.I_error.inf ++ List.ofFn Z.I_error.sup

/-- The sets of a successful step: `R_0` from `Rti`, `X_1` from `Rtp`, and the status they earn. -/
def aux_sets (nonFinite : 𝕋 → Bool) (X0 : Zonotope (Vec 𝕋 2)) (etaUsed : ℕ)
    (Rti Rtp : List (Zonotope (Vec 𝕋 2))) : Option (String × String × List (String × Json)) :=
  match Rti, Rtp with
  | R0 :: _, _ :: X1 :: _ =>
    -- a scalar past the range is `null` in the sets, and the whole record says so
    let bad := (aux_scalars X0 ++ aux_scalars R0 ++ aux_scalars X1).any nonFinite
    let extra := [("eta_used", Lean.toJson etaUsed),
      ("R0", zonotopeRatJson nonFinite R0), ("X1", zonotopeRatJson nonFinite X1)]
    some (if bad then
      ("overflow-NaN", "a stored scalar is past the format's range or NaN", extra)
    else ("ok", "", extra))
  | _, _ => none

/-- The record's `status`, `reason` and whatever else it can say, in that order. -/
def aux_result (cfg : HeadlineConfig) (inst : String → ExactDyadic → Except String 𝕋)
    (exactIn : ExactDyadic → 𝕋) (nt : NumberType 𝕋) (dtStr : String) :
    String × String × List (String × Json) :=
  let nonFinite : 𝕋 → Bool := nt.overflows.getD fun _ => false
  let none' (reason : String) (extra : List (String × Json)) := ("none", reason, extra)
  -- X0 first: a record that fails later still says what X0 the format holds
  match roundX0In cfg exactIn with
  | .error e => none' e []
  | .ok X0 =>
  let x0J := [("x0", zonotopeRatJson nonFinite X0)]
  match parseExact dtStr with
  | .error e => none' s!"dt: {e}" x0J
  | .ok dtE =>
  -- `A` and `dt` exactly, as `buildContSystem` reads them
  match inst "dt" dtE, (do
      let a ← inst "system.a" (← parseExact cfg.a)
      let b ← inst "system.b" (← parseExact cfg.b)
      let nb ← inst "system.b" (← parseExact cfg.b).neg
      pure (Matrix.of ![![a, b], ![nb, a]] : Mat 𝕋 2 2)) with
  | .error e, _ | _, .error e => none' s!"not representable: {e}" x0J
  | .ok dt, .ok A =>
  let sys : LinearSys 𝕋 2 := LinearSys.canonicalFloat A
  let dtJ := [("dt_represented", ratJson (ToRat.toRat dt))]
  let params : Reach.Params (Zonotope (Vec 𝕋 2)) ℚ := { X₀ := X0, tFinal := ToRat.toRat dt }
  let options : LinearSys.ReachOptions 𝕋 :=
    { Δt := dt, η := cfg.eta, ρ := cfg.rho }
  -- the order check ahead of `reachFloat`, as `Registry.aux_runTiTp`, for a clear reason
  match sys.reachOrderFloat dt dt cfg.eta with
  | none => none' s!"no admissible Taylor order (from max {cfg.eta} 2) found within the \
search bound"
      (x0J ++ dtJ)
  | some etaUsed =>
  match sys.reachFloat params options with
  | none => none' s!"Reach.steps or a window's squaring search returned none (eta = {etaUsed})"
      (x0J ++ dtJ)
  | some (Rti, Rtp) =>
  match aux_sets nonFinite X0 etaUsed Rti Rtp with
  | some (st, reason, extra) => (st, reason, x0J ++ dtJ ++ extra)
  | none => none' "reachFloat returned fewer sets than one step gives" (x0J ++ dtJ)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The record for one number type and one `dt`: `head` (`type`, `format`, ...) beside `dt`,
`status`, `reason` and the sets. `exactIn` holds an exact value in the format, off its grid. -/
def firstStepRecord (cfg : HeadlineConfig) (head : List (String × Json))
    (inst : String → ExactDyadic → Except String 𝕋) (exactIn : ExactDyadic → 𝕋)
    (nt : NumberType 𝕋) (dtStr : String) : Json :=
  let (status, reason, extra) := aux_result cfg inst exactIn nt dtStr
  Json.mkObj (head ++ [("dt", Json.str dtStr), ("status", Json.str status),
    ("reason", Json.str reason)] ++ extra)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
