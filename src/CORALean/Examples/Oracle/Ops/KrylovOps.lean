import CORALean.ContDynamics.LinearSys.Krylov.Operations.SubspaceFloat
import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowsFloat
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The Krylov ops: the float Arnoldi iteration and its certified order

`krylov.arnoldi` runs `Krylov.arnoldiFloat` for `passes` passes on `A` and the start vector `c`
(`nu` its norm); `krylov.errorBound` evaluates, for the Arnoldi data of `order` passes, the bound
`Krylov.errorBoundFloat` with its factors and the test `Krylov.orderOkFloat`; `krylov.subspace`
runs `Krylov.subspaceFloat`, the order search from `k0` in steps of `step`; `krylov.windows` adds
the windows of the subspace's small system (`Krylov.windowsFloat`). `A` is square, `c` a column,
`eps` the breakdown threshold, `tf` the final time, `tol` the tolerance; `p` and `q` default to 20
and 10. Bases and Hessenberg matrices come back as matrices, `V` of `n` rows.

## Inputs
* `dops` – dtype operations
* `name` – op name without the `krylov.` prefix
* `req` – request

## Output
* the response fields, or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A natural number field, or the default when absent. -/
private def aux_natOr (req : Json) (name : String) (d : Nat) : Except String Nat :=
  match fieldOpt req name with
  | none => pure d
  | some _ => natField req name

/-- A scalar field read exactly into the dtype. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 :=
  dops.readExact name =<< scalarField req name

/-- The square matrix `A` of the request and the start vector `c`, the dimension read off `A`. -/
private def aux_problem (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, Mat 𝕋 n n × Vec 𝕋 n) := do
  let dA ← parseMatDyn dops.readExact (← field req "A")
  if hA : dA.r = dA.c then
    let A : Mat 𝕋 dA.r dA.r := cast (congrArg (Mat 𝕋 dA.r) hA.symm) dA.M
    pure ⟨dA.r, A, ← parseVecFixed dops.readExact dA.r (← field req "c")⟩
  else throw s!"`A` must be square, not {dA.r}×{dA.c}"

/-- An exact scalar as an exact fraction. -/
private def aux_ratOf : ExactScalar → ℚ
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat : ℤ) else (m : ℚ) / (2 ^ (-e).toNat : ℕ)
  | .decNeg m d => (m : ℚ) / (10 ^ d : ℕ)

/-- The basis `V(0), …, V(k)` as the `n × (k + 1)` matrix. -/
private def aux_basis {n : Nat} (V : Nat → Vector 𝕋 n) (k : Nat) : Mat 𝕋 n (k + 1) :=
  fun r j => (V j)[r]

/-- The Hessenberg entries as the `(k + 1) × k` matrix. -/
private def aux_hess (H : Nat → Nat → 𝕋) (k : Nat) : Mat 𝕋 (k + 1) k := fun i j => H i j

/-- The common fields of the Arnoldi data of `k` passes. -/
private def aux_data (dops : DtypeOps 𝕋) {n : Nat} (V : Nat → Vector 𝕋 n) (H : Nat → Nat → 𝕋)
    (k : Nat) : List (String × Json) :=
  [("V", printMat dops.showExact (aux_basis V k)), ("H", printMat dops.showExact (aux_hess H k))]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `"krylov.<name>"`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleKrylovOp (dops : DtypeOps 𝕋) (name : String) (req : Json) : Option Resp :=
  match name with
  -- Alg. 1 in floats
  | "arnoldi" => some (do
    checkFields "krylov.arnoldi" req ["A", "c", "passes", "eps", "p"]
    let ⟨_, A, c⟩ ← aux_problem dops req
    let p ← aux_natOr req "p" 20
    let k ← natField req "passes"
    let eps ← aux_scalar dops req "eps"
    let ν := Float.normUp p c
    let st := Krylov.arnoldiFloat p eps A c ν k
    pure (("nu", Json.str (dops.showExact ν)) :: aux_data dops st.1 st.2 k))
  -- the bound of the error of `order` passes, its factors and the test
  | "errorBound" => some (do
    checkFields "krylov.errorBound" req ["A", "c", "order", "tf", "tol", "eps", "p", "q"]
    let ⟨_, A, c⟩ ← aux_problem dops req
    let p ← aux_natOr req "p" 20
    let q ← aux_natOr req "q" 10
    let k ← natField req "order"
    let eps ← aux_scalar dops req "eps"
    let tf ← aux_scalar dops req "tf"
    let tol ← aux_scalar dops req "tol"
    let ν := Float.normUp p c
    let st := Krylov.arnoldiFloat p eps A c ν k
    -- the residual norms of the stored columns, the discs of `A` and of `T_k`
    let res := fun j => Krylov.residualNormFloat p A st.1 st.2 j
    let μA := Krylov.quadBoundUp A
    let μT := Krylov.quadBoundUp fun i j : Fin k => st.2 i j
    pure ([("nu", Json.str (dops.showExact ν)),
      ("residuals", Json.arr ((List.range k).toArray.map fun j =>
        Json.str (dops.showExact (res j)))),
      ("muA", Json.str (dops.showExact μA)), ("muT", Json.str (dops.showExact μT)),
      ("bound", Json.str (dops.showExact (Krylov.errorBoundFloat p q μA res c ν st.1 st.2 k tf))),
      ("ok", Json.bool (decide (1 ≤ k) &&
        Krylov.orderOkFloat p q μA res c ν st.1 st.2 k tf tol))] ++ aux_data dops st.1 st.2 k))
  -- the order search
  | "subspace" => some (do
    checkFields "krylov.subspace" req
      ["A", "c", "k0", "step", "tf", "tol", "eps", "p", "q", "fuel"]
    let ⟨n, A, c⟩ ← aux_problem dops req
    let p ← aux_natOr req "p" 20
    let q ← aux_natOr req "q" 10
    let fuel ← aux_natOr req "fuel" (n + 1)
    let r := Krylov.subspaceFloat p q (← aux_scalar dops req "eps") A c (← natField req "k0")
      (← natField req "step") (← aux_scalar dops req "tf") (← aux_scalar dops req "tol") fuel
    pure ([("order", Lean.toJson r.order), ("ok", Json.bool r.ok),
      ("bound", Json.str (dops.showExact r.bound)), ("nu", Json.str (dops.showExact r.ν))] ++
      aux_data dops r.V r.H r.order))
  -- the time-point and time-interval sets of the subspace's `k`-dimensional system
  | "windows" => some (do
    checkFields "krylov.windows" req
      ["A", "c", "k0", "step", "tFinal", "tol", "eps", "p", "q", "fuel", "timeStep",
        "taylorTerms", "zonotopeOrder"]
    let ⟨n, A, c⟩ ← aux_problem dops req
    let p ← aux_natOr req "p" 20
    let q ← aux_natOr req "q" 10
    let fuel ← aux_natOr req "fuel" (n + 1)
    let tf ← aux_scalar dops req "tFinal"
    -- the subspace, then its windows if the order was accepted
    let r := Krylov.subspaceFloat p q (← aux_scalar dops req "eps") A c (← natField req "k0")
      (← natField req "step") tf (← aux_scalar dops req "tol") fuel
    let head := [("order", Lean.toJson r.order), ("ok", Json.bool r.ok),
      ("bound", Json.str (dops.showExact r.bound)), ("nu", Json.str (dops.showExact r.ν))] ++
      aux_data dops r.V r.H r.order
    if !r.ok then pure (head ++ [("timeInterval", Json.null), ("timePoint", Json.null)])
    else
      -- the time step is read exactly, the time grid unchanged
      let Δt ← dops.readExact "timeStep" (← scalarField req "timeStep")
      match Krylov.windowsFloat r Δt (aux_ratOf (← scalarField req "tFinal"))
          (← natField req "taylorTerms") (← natField req "zonotopeOrder") with
      | none => throw "krylov.windows: no admissible Taylor order was found for this timeStep"
      | some (Rti, Rtp) =>
        pure (head ++ [("timeInterval", Json.arr (Rti.toArray.map (printZonotope dops.showExact))),
          ("timePoint", Json.arr (Rtp.toArray.map (printZonotope dops.showExact)))]))
  | _ => none

/-- Every op of this file, without the `krylov.` prefix. -/
def krylovOpNames : List String := ["arnoldi", "errorBound", "subspace", "windows"]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
