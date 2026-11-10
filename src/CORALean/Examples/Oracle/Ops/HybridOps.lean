import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContSet.ZonoBundle.Float.Instances
import CORALean.Examples.Oracle.Ops.LinearSysOps
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.HybridDynamics.Operations.CalcBasisBox
import CORALean.HybridDynamics.Operations.GuardGroups
import CORALean.HybridDynamics.Operations.CheckFlowFloat
import CORALean.HybridDynamics.Operations.GuardIntersectNondetFloat
import CORALean.HybridDynamics.Operations.GuardIntersectNondetHFloat
import CORALean.HybridDynamics.Operations.GuardIntersectPolytopeFloat
import CORALean.HybridDynamics.Operations.GuardIntersectPolytopeHFloat
import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
import CORALean.HybridDynamics.Operations.InputSetFloat
import CORALean.HybridDynamics.Operations.JumpFloat
import CORALean.HybridDynamics.Operations.LocationPotInt
import CORALean.HybridDynamics.Operations.LocationReachFloat
import CORALean.Specification.Instances

/-!
# The hybrid-automaton ops: CORA's `location` and `transition` steps

Thin adapters over the float definitions `references/coverage/hybridDynamics/location.md` links;
the wire shapes are in `experiments/oracle/README.md`. A location is the flow `A`, `B`, `c`, `E` of
`linearSys` with the input sets `U`, `W` (the origin when absent); invariant and transitions are not
needed by these steps. Indices are 0-based. A field an op does not list is refused by name.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero matrix. -/
private def aux_zeroMat (r c : Nat) : Mat 𝕋 r c := fun _ _ => FloatOps.zero

/-- A location of the flow `sys` with the input sets `U`, `W`, no invariant and the transitions
`trans`. -/
private def aux_location {n : Nat} (sys : LinearSys 𝕋 n) (U : Zonotope (Vec 𝕋 sys.m))
    (W : Zonotope (Vec 𝕋 sys.r)) (trans : List (Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k))
      Nat 𝕋 n)) : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) Nat 𝕋 n :=
  ⟨HPolytope.fullspace 𝕋 n, sys, U, W, trans⟩

/-- The location of the request's flow: `A`, `B`, `c`, `E`, and the input sets `U`, `W`. -/
private def aux_flowLocation (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) Nat 𝕋 n) := do
  let d ← parseLinearSys dops req
  let U ← match fieldOpt req "U" with
    | some j => parseZonotopeFixed dops.readExact d.sys.m j
    | none => pure (Zonotope.origin (𝕋 := 𝕋) d.sys.m)
  let W ← match fieldOpt req "W" with
    | some j => parseZonotopeFixed dops.readExact d.sys.r j
    | none => pure (Zonotope.origin (𝕋 := 𝕋) d.sys.r)
  pure ⟨d.n, aux_location d.sys U W []⟩

/-- A zonotope list of the dimension `n` in field `name`. -/
private def aux_zonos (dops : DtypeOps 𝕋) (req : Json) (name : String) (n : Nat) :
    Except String (List (Zonotope (Vec 𝕋 n))) := do
  pure (← (← arrField req name).mapM (parseZonotopeFixed dops.readExact n)).toList

/-- The bases `Bs`, matrices `n × n`. -/
private def aux_bases (dops : DtypeOps 𝕋) (req : Json) (n : Nat) :
    Except String (List (Mat 𝕋 n n)) := do
  let js ← arrField req "Bs"
  let bs ← js.mapM fun j => do
    let ⟨r, M⟩ ← parseMatColsFixed dops.readExact n j
    if h : r = n then pure (h ▸ M : Mat 𝕋 n n)
    else throw s!"a basis has {r} rows, expected {n}"
  pure bs.toList

/-- The dimension of the zonotope `R0`. -/
private def aux_dim (req : Json) (name : String) : Except String Nat :=
  do natField (← field (← field req name) "c") "rows"

/-- `n`, `R0`, `R`, the bases of a guard-intersection request. -/
private def aux_guardInput (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, List (Mat 𝕋 n n) × Zonotope (Vec 𝕋 n) ×
      List (Zonotope (Vec 𝕋 n))) := do
  let n ← aux_dim req "R0"
  pure ⟨n, ← aux_bases dops req n, ← parseZonotopeFixed dops.readExact n (← field req "R0"),
    ← aux_zonos dops req "R" n⟩

/-- `a` as an exact fraction. -/
private def aux_ratOf : ExactScalar → ℚ
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat : ℤ) else (m : ℚ) / (2 ^ (-e).toNat : ℕ)
  | .decNeg m d => (m : ℚ) / (10 ^ d : ℕ)

/-- The zonotope reduced to `order`, `Reduce.reduce`. -/
private def aux_reduce {n : Nat} (order : Nat) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  Reduce.reduce Z order


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `location.potInt`: `Location.potInt`, the `(transition, set)` pairs whose guard may meet the
set, the transitions into `finalLoc` skipped. -/
def handleLocationPotInt (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "potInt" req ["guards", "targets", "finalLoc", "R"]
  -- the transitions: one guard each, into the location `targets` names
  let gs ← arrField req "guards"
  let Rj ← arrField req "R"
  let targets ← natArrField req "targets"
  if targets.size ≠ gs.size then throw "potInt: `targets` and `guards` differ in length"
  let n ← if h : 0 < Rj.size then natField (← field Rj[0] "c") "rows"
    else if h : 0 < gs.size then natField (← field gs[0] "A") "cols"
    else pure 0
  let trans ← (gs.zip targets).mapM fun (g, t) => do
    let guard ← parseHPolytopeFixed dops.readExact n g
    pure (⟨guard, aux_zeroMat n n, fun _ => FloatOps.zero, t⟩ :
      Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) Nat 𝕋 n)
  let Rs ← Rj.mapM (parseZonotopeFixed dops.readExact n)
  -- the flow is not read by `potInt`: a location with the zero flow carries the guards
  let finalLoc ← natField req "finalLoc"
  let sys : LinearSys 𝕋 n := ⟨0, 0, 0, 0, aux_zeroMat n n, aux_zeroMat n 0, fun _ => FloatOps.zero,
    aux_zeroMat 0 n, aux_zeroMat 0 0, fun _ => FloatOps.zero, aux_zeroMat n 0, aux_zeroMat 0 0⟩
  let ℓ := aux_location sys (Zonotope.origin 0) (Zonotope.origin 0) trans.toList
  let hits := Location.potInt ℓ Rs.toList finalLoc
  pure [("hits", Json.arr (hits.toArray.map fun (i, j) =>
    Json.arr #[Lean.toJson i, Lean.toJson j]))]

/-- `location.calcBasis`: `Location.calcBasisBox`, the `box` basis `eye(n)`. -/
def handleLocationCalcBasis (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "calcBasis" req ["n", "enclose"]
  let n ← natField req "n"
  let names ← match ← field req "enclose" with
    | .arr a => a.mapM fun j => match j.getStr? with
      | .ok s => pure s
      | .error _ => throw "calcBasis: `enclose` must hold strings"
    | .str s => pure #[s]
    | _ => throw "calcBasis: `enclose` must be a string or a list of strings"
  let Bs ← names.mapM fun s =>
    if s = "box" then pure (printMat dops.showExact (Location.calcBasisBox 𝕋 n))
    else throw s!"calcBasis: `{s}` has no float definition, only `box`"
  pure [("B", Json.arr Bs)]

/-- `location.checkFlow`: `Location.checkFlowFloat`, per set. -/
def handleLocationCheckFlow (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "checkFlow" req ["A", "B", "c", "E", "U", "W", "hyperplane", "R"]
  let ⟨n, ℓ⟩ ← aux_flowLocation dops req
  let hp ← field req "hyperplane"
  let nrm ← parseVecFixed dops.readExact n (← field hp "normal")
  let d ← dops.readExact "d" (← scalarField hp "d")
  let Rs ← aux_zonos dops req "R" n
  let keep := Rs.zipIdx.filterMap fun (R, i) =>
    if (ℓ.checkFlowFloat nrm d [R]).isEmpty then none else some i
  pure [("keep", Json.arr (keep.toArray.map Lean.toJson))]

/-- `location.guardIntersect_zonoGirard`: `Location.guardIntersectZonoGirardFloat`. -/
def handleGuardZonoGirard (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "guardIntersect_zonoGirard" req ["Bs", "R0", "R", "normal", "gamma"]
  let ⟨n, Bs, R0, Rs⟩ ← aux_guardInput dops req
  let nv ← parseVecFixed dops.readExact n (← field req "normal")
  let γ ← dops.readExact "gamma" (← scalarField req "gamma")
  let zB := Location.guardIntersectZonoGirardFloat Bs R0 Rs nv γ
  pure [("zB", printZonoBundle dops.showExact zB)]

/-- The guard of a request: a constrained zonotope when it has generators `G`, else a halfspace
polytope `A`, `b`, `Ae`, `be`. -/
private def aux_guard (dops : DtypeOps 𝕋) (req : Json) (n : Nat) :
    Except String (ConZonotope 𝕋 (Vec 𝕋 n) ⊕ HPolytope 𝕋 (Vec 𝕋 n)) := do
  let g ← field req "guard"
  if (fieldOpt g "G").isSome then pure (.inl (← parseConZonotopeFixed dops.readExact n g))
  else pure (.inr (← parseHPolytopeFixed dops.readExact n g))

/-- The contraction passes `fmPasses` of the box of a cut, asked for with a polytope guard. -/
private def aux_passes (req : Json) : Except String Nat := do
  if (fieldOpt req "fmPasses").isSome then natField req "fmPasses"
  else throw "a polytope guard needs `fmPasses`, the Fourier-Motzkin passes of the box of a cut"

/-- `location.guardIntersect_nondetGuard`: `Location.guardIntersectNondetFloat` for a constrained
zonotope guard, `Location.guardIntersectNondetHFloat` for a polytope guard (`fmPasses`). -/
def handleGuardNondet (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "guardIntersect_nondetGuard" req ["Bs", "R0", "R", "guard", "fmPasses"]
  let ⟨n, Bs, R0, Rs⟩ ← aux_guardInput dops req
  match ← aux_guard dops req n with
  | .inl guard =>
    if (fieldOpt req "fmPasses").isSome then throw "`fmPasses` is for a polytope guard"
    pure [("zB", printZonoBundle dops.showExact
      (Location.guardIntersectNondetFloat Bs R0 Rs guard))]
  | .inr guard =>
    pure [("zB", printZonoBundle dops.showExact
      (Location.guardIntersectNondetHFloat (← aux_passes req) Bs R0 Rs guard))]

/-- `location.guardIntersect_conZonotope`: `Location.guardIntersectPolytopeFloat` on the sets
reduced to `guardOrder`, for a constrained zonotope guard, `Location.guardIntersectPolytopeHFloat`
for a polytope guard (`fmPasses`). -/
def handleGuardConZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "guardIntersect_conZonotope" req ["Bs", "R0", "R", "guard", "guardOrder", "fmPasses"]
  let ⟨n, Bs, R0, Rs⟩ ← aux_guardInput dops req
  let order ← natField req "guardOrder"
  match ← aux_guard dops req n with
  | .inl guard =>
    if (fieldOpt req "fmPasses").isSome then throw "`fmPasses` is for a polytope guard"
    pure [("zB", printZonoBundle dops.showExact (Location.guardIntersectPolytopeFloat Bs
      (aux_reduce order R0) (Rs.map (aux_reduce order)) guard))]
  | .inr guard =>
    pure [("zB", printZonoBundle dops.showExact (Location.guardIntersectPolytopeHFloat
      (← aux_passes req) Bs (aux_reduce order R0) (Rs.map (aux_reduce order)) guard))]

/-- `location.guardGroups`: `Location.guardGroups`, the hits grouped by guard and split at gaps. -/
def handleLocationGuardGroups (_dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "guardGroups" req ["hits"]
  let hits ← (← arrField req "hits").mapM fun h => do
    let a ← match h with
      | .arr a => pure a
      | _ => throw "guardGroups: every hit is `[transition, set]`"
    if a.size ≠ 2 then throw "guardGroups: every hit is `[transition, set]`"
    match a[0]!.getNat?, a[1]!.getNat? with
    | .ok t, .ok i => pure (t, i)
    | _, _ => throw "guardGroups: a hit holds natural numbers"
  let groups := Location.guardGroups hits.toList
  pure [("groups", Json.arr (groups.toArray.map fun (g, r) => Json.mkObj
    [("transition", Lean.toJson g), ("sets", Json.arr (r.toArray.map Lean.toJson)),
     ("minInd", Lean.toJson (r.headD 0)), ("maxInd", Lean.toJson (r.getLastD 0))]))]

/-- `location.reach`: `Location.reachFloat`, one stay from `X0`, the horizon `tFinal` in steps of
`timeStep`. -/
def handleLocationReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reach" req ["A", "B", "c", "E", "U", "W", "X0", "tFinal", "timeStep",
    "taylorTerms", "zonotopeOrder"]
  let ⟨n, ℓ⟩ ← aux_flowLocation dops req
  let X0 ← parseZonotopeFixed dops.readExact n (← field req "X0")
  let tFinal ← scalarField req "tFinal"
  let Δt ← dops.readExact "timeStep" (← scalarField req "timeStep")
  let options : LinearSys.ReachOptions 𝕋 :=
    { Δt := Δt, η := ← natField req "taylorTerms", ρ := ← natField req "zonotopeOrder" }
  match ℓ.reachFloat (aux_ratOf tFinal) options X0 with
  | none => throw "reach: no admissible Taylor order was found, or tFinal/timeStep is not a \
      positive integer"
  | some Rti => pure [("timeInterval", Json.arr (Rti.toArray.map (printZonotope dops.showExact)))]

/-- `transition.jump`: `Transition.jumpFloat`, `W Rg + w`. -/
def handleTransitionJump (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "jump" req ["W", "w", "Rg"]
  let dR ← parseZonotope dops.readExact (← field req "Rg")
  let ⟨r, W⟩ ← parseMatColsFixed dops.readExact dR.n (← field req "W")
  let w ← parseVecFixed dops.readExact r (← field req "w")
  if h : r = dR.n then
    let e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) Nat 𝕋 dR.n :=
      ⟨HPolytope.fullspace 𝕋 dR.n, h ▸ W, h ▸ w, 0⟩
    pure [("Z", printZonotope dops.showExact (e.jumpFloat dR.Z))]
  else throw s!"jump: `W` has {r} rows, expected {dR.n}; a reset to another dimension is not \
    modelled"

/-- Every op of this file, without the `location.` and `transition.` prefixes. -/
def locationOpNames : List String :=
  [ "potInt", "calcBasis", "checkFlow", "guardIntersect_zonoGirard", "guardIntersect_nondetGuard",
    "guardIntersect_conZonotope", "guardGroups", "reach" ]

/-- `op` of `location.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleLocationOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "potInt" => some (handleLocationPotInt dops req)
  | "calcBasis" => some (handleLocationCalcBasis dops req)
  | "checkFlow" => some (handleLocationCheckFlow dops req)
  | "guardIntersect_zonoGirard" => some (handleGuardZonoGirard dops req)
  | "guardIntersect_nondetGuard" => some (handleGuardNondet dops req)
  | "guardIntersect_conZonotope" => some (handleGuardConZonotope dops req)
  | "guardGroups" => some (handleLocationGuardGroups dops req)
  | "reach" => some (handleLocationReach dops req)
  | _ => none

/-- Every op of `transition.`. -/
def transitionOpNames : List String := [ "jump" ]

/-- `op` of `transition.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleTransitionOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "jump" => some (handleTransitionJump dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
