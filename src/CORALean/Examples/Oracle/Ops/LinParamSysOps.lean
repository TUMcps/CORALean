import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInput
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The linear-parametric-system ops: CORA's `linParamSys` reach

Thin adapters over `LinParamSys.reachFloat` and `.reachFloatInput`, the float definitions
`references/coverage/contDynamics/linParamSys.md` links; the wire shape is in
`experiments/oracle/README.md`. `A` stays an interval matrix and window `k` comes from the first
by `[e^{[A] t_k}]`, not from CORA's `post`; the Taylor order is raised until admissible.

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

/-- `a` as an exact fraction. -/
private def aux_ratOf : ExactScalar → ℚ
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat : ℤ) else (m : ℚ) / (2 ^ (-e).toNat : ℕ)
  | .decNeg m d => (m : ℚ) / (10 ^ d : ℕ)

/-- The interval matrix `d`, square. -/
private def aux_square (d : DynBoxMat 𝕋) (h : d.r = d.c) : Interval (Mat 𝕋 d.r d.r) :=
  match d, h with
  | ⟨_, _, I⟩, rfl => I

/-- The interval matrix `d` read with `n` rows. -/
private def aux_rows (d : DynBoxMat 𝕋) (n : Nat) (h : d.r = n) : Interval (Mat 𝕋 n d.c) :=
  match d, n, h with
  | ⟨_, _, I⟩, _, rfl => I

/-- A zonotope list as the response array. -/
private def aux_zs (dops : DtypeOps 𝕋) {n : Nat} (l : List (Zonotope (Vec 𝕋 n))) : Json :=
  Json.arr (l.toArray.map (printZonotope dops.showExact))

/-- An interval matrix field: `{"inf","sup"}`, or a plain matrix as the point interval. -/
private def aux_intervalMat (dops : DtypeOps 𝕋) (j : Json) : Except String (DynBoxMat 𝕋) :=
  match fieldOpt j "inf" with
  | some _ => parseBoxMat dops.readExact j
  | none => do
    let d ← parseMatDyn dops.readExact j
    pure ⟨d.r, d.c, ⟨d.M, d.M⟩⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linParamSys.reach`: `LinParamSys.reachFloat`, or `reachFloatInput` with `B`, `c` or `U`. -/
def handleLinParamSysReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reach" req ["A", "B", "c", "X0", "U", "tStart", "tFinal", "timeStep",
    "taylorTerms", "zonotopeOrder"]
  -- the system: `A` square, `B` and `c` optional
  let dA ← aux_intervalMat dops (← field req "A")
  if hA : dA.r = dA.c then
    let n := dA.r
    let A : Interval (Mat 𝕋 n n) := aux_square dA hA
    let mB : Σ m : Nat, Interval (Mat 𝕋 n m) ← match fieldOpt req "B" with
      | none => pure ⟨0, ⟨fun _ _ => FloatOps.zero, fun _ _ => FloatOps.zero⟩⟩
      | some j => do
        let d ← aux_intervalMat dops j
        if h : d.r = n then
          pure ⟨d.c, aux_rows d n h⟩
        else throw s!"`B` has {d.r} rows, expected {n}"
    let ⟨m, B⟩ := mB
    let c ← match fieldOpt req "c" with
      | none => pure (fun _ => FloatOps.zero : Vec 𝕋 n)
      | some j => parseVecFixed dops.readExact n j
    let sys : LinParamSys ℐ[𝕋] n := ⟨A, m, B, fun _ => 0⟩
    -- the time grid and the options, exactly as `linearSys.reach` reads them
    let X0 ← parseZonotopeFixed dops.readExact n (← field req "X0")
    let tStart := match fieldOpt req "tStart" with
      | none => (0 : ℚ)
      | some _ => 0
    let tStart ← match fieldOpt req "tStart" with
      | none => pure tStart
      | some _ => pure (aux_ratOf (← scalarField req "tStart"))
    let tFinal := aux_ratOf (← scalarField req "tFinal")
    let Δt ← dops.readExact "timeStep" (← scalarField req "timeStep")
    let options : LinearSys.ReachFloatOptions 𝕋 :=
      { Δt := Δt, η := ← natField req "taylorTerms", ρ := ← natField req "zonotopeOrder" }
    let hasInput := (fieldOpt req "U").isSome || (fieldOpt req "B").isSome ||
      (fieldOpt req "c").isSome
    let fail := "reach: no admissible Taylor order was found, or (tFinal - tStart)/timeStep is \
      not a nonnegative integer"
    -- an input set, `B` or an offset `c` is the input variant
    if hasInput then
      let U ← match fieldOpt req "U" with
        | some j => parseZonotopeFixed dops.readExact m j
        | none => pure (Zonotope.origin (𝕋 := 𝕋) m)
      let params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ :=
        { X₀ := X0, U := U, tStart := tStart, tFinal := tFinal }
      match sys.reachFloatInput c params options with
      | none => throw fail
      | some Rti => pure [("timeInterval", aux_zs dops Rti)]
    else
      let params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ :=
        { X₀ := X0, tStart := tStart, tFinal := tFinal }
      match sys.reachFloat params options with
      | none => throw fail
      | some Rti => pure [("timeInterval", aux_zs dops Rti)]
  else throw s!"`A` must be square, not {dA.r}×{dA.c}"

/-- Every op of this file, without the `linParamSys.` prefix. -/
def linParamSysOpNames : List String := [ "reach" ]

/-- `op` of `linParamSys.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleLinParamSysOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "reach" => some (handleLinParamSysReach dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
