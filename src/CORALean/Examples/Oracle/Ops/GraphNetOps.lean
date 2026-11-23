import CORALean.NN.Operations.EvaluateGraph
import CORALean.NN.Layers.Operations.ReluRelaxation
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Layers.Operations.SignRelaxation
import CORALean.NN.Layers.Operations.SquareChordTangentRelaxation
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The op `neuralNetwork.evaluateGraph`: a graph network on a zonotope

CORA.cpp's `ZonoNet::forward` on a network with sources and residuals. A layer is `W`, `b`, the
`source` it reads (CORA.cpp's index: `-1` the input, `j` the output of layer `j`; by default the
layer before), its `residuals` (each a `source` and a map `R`, the identity without one), its
`activation` (`identity`, `relu`, `sign`, `square` or `product`, the last with `p` and `tiny`) and
its `slots` (`all`, the default, or `none`: the errors as generators or in the error box).
`Float.GraphNet.evaluateGraph`; sound by `GraphNet.evaluateGraph_encloses`.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* the last output's zonotope, `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `N * 2⁻⁵²`, CORA.cpp's `N eps` of binary64 (exact for `N < 2⁵³`; zero if unreadable). -/
private def aux_epsOf (dops : DtypeOps 𝕋) (N : ℕ) : 𝕋 :=
  match scalarField (Json.mkObj [("eps", Json.str s!"{N}*2^-52")]) "eps" with
  | .ok v => (dops.readExact "eps" v).toOption.getD FloatOps.zero
  | .error _ => FloatOps.zero

/-- The place in `Γ` (the latest output first) of CORA.cpp's source `s` of layer `k`. -/
private def aux_place (Γ : List ℕ) (k : ℕ) (s : Int) : Except String (Fin Γ.length) :=
  let p := (k : Int) - 1 - s
  if h : 0 ≤ p ∧ p.toNat < Γ.length then pure ⟨p.toNat, h.2⟩
  else throw s!"evaluateGraph: layer {k} reads `source` {s}, which is not an earlier output"

/-- The `source` of `j`, CORA.cpp's index, by default the layer before `k`. -/
private def aux_source (j : Json) (k : ℕ) : Except String Int :=
  match fieldOpt j "source" with
  | none => pure ((k : Int) - 1)
  | some v => match v.getInt? with
    | .ok s => pure s
    | .error _ => throw "evaluateGraph: `source` is an integer"

/-- A residual of layer `k` with `m` outputs: its source, through `R` or the identity. -/
private def aux_residual (dops : DtypeOps 𝕋) (Γ : List ℕ) (k m : ℕ) (j : Json) :
    Except String (GraphResidual 𝕋 Γ m) := do
  checkFields "evaluateGraph" j ["source", "R"]
  let src ← aux_place Γ k (← aux_source j k)
  match fieldOpt j "R" with
  | some rj =>
    let ⟨r, R⟩ ← parseMatColsFixed dops.readExact (Γ.get src) rj
    if h : r = m then pure ⟨src, h ▸ R⟩
    else throw s!"evaluateGraph: a residual of layer {k} maps to {r}, not {m}"
  | none =>
    if Γ.get src = m then
      pure ⟨src, fun i l => if i.1 = l.1 then FloatOps.one else FloatOps.zero⟩
    else throw s!"evaluateGraph: a residual of layer {k} without `R` needs {m} entries"

/-- The activation of layer `k` with `m` outputs; `slots` all or none. -/
private def aux_act (dops : DtypeOps 𝕋) (k m : ℕ) (j : Json) :
    Except String (Σ m' : ℕ, PLift (m' = m) × GraphAct 𝕋 m') := do
  let slots ← match (fieldOpt j "slots").bind (·.getStr?.toOption) with
    | none | some "all" => pure true
    | some "none" => pure false
    | some s => throw s!"evaluateGraph: `slots` is all or none, not `{s}`"
  match (fieldOpt j "activation").bind (·.getStr?.toOption) with
  | none | some "identity" => pure ⟨m, ⟨rfl⟩, .identity⟩
  | some "relu" => pure ⟨m, ⟨rfl⟩, .elementwise (reluRelaxation reluSlope) slots⟩
  | some "sign" => pure ⟨m, ⟨rfl⟩, .elementwise signRelaxation slots⟩
  | some "square" => pure ⟨m, ⟨rfl⟩,
      .elementwise (squareChordTangentRelaxation (FloatOps.half^[49] FloatOps.one)) slots⟩
  | some "product" =>
    if h : m % 2 = 0 then
      let p ← natField j "p"
      let tj := (fieldOpt j "tiny").getD (Json.str "6032057205060441*2^-1049")
      let τ ← dops.readExact "tiny" (← scalarField (Json.mkObj [("tiny", tj)]) "tiny")
      -- CORA.cpp's margins: (2 (q + 2) + 16) eps at q generators, and 16 eps
      pure ⟨m / 2 + m / 2, ⟨by omega⟩, .product (m / 2) p τ (FloatOps.half^[48] FloatOps.one)
        (fun q => aux_epsOf dops (2 * (q + 2) + 16)) slots⟩
    else throw s!"evaluateGraph: the product of layer {k} needs an even width, not {m}"
  | some a => throw s!"evaluateGraph: `activation` must be identity, relu, sign, square or \
      product, not `{a}`"

/-- The layers from the `k`-th on, after the outputs `Γ`. -/
private def aux_build (dops : DtypeOps 𝕋) :
    (Γ : List ℕ) → ℕ → List Json → Except String (Σ k, GraphNet 𝕋 Γ k)
  | [], _, _ => throw "evaluateGraph: no input"
  | m :: _, _, [] => pure ⟨m, .done⟩
  | Γ, k, layer :: rest => do
    checkFields "evaluateGraph" layer
      ["W", "b", "source", "residuals", "activation", "slots", "p", "tiny"]
    let src ← aux_place Γ k (← aux_source layer k)
    let ⟨m, W⟩ ← parseMatColsFixed dops.readExact (Γ.get src) (← field layer "W")
    let b ← parseVecFixed dops.readExact m (← field layer "b")
    let rs ← match fieldOpt layer "residuals" with
      | none => pure []
      | some _ => (← arrField layer "residuals").toList.mapM (aux_residual dops Γ k m)
    -- the activation at its own width, the layer's data carried over
    let ⟨m', ⟨h⟩, act⟩ ← aux_act dops k m layer
    let L : GraphLayer 𝕋 Γ m' := ⟨src, h ▸ W, h ▸ b, h ▸ rs, act⟩
    let ⟨k', tail⟩ ← aux_build dops (m' :: Γ) (k + 1) rest
    pure ⟨k', .layer L tail⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The graph network of `layers` on the zonotope `Z`: the last output's zonotope. -/
def evaluateGraphOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "evaluateGraph" req ["layers", "Z"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, net⟩ ← aux_build dops [dz.n] 0 (← arrField req "layers").toList
  pure [("Z", printZonotope dops.showExact (net.evaluateGraph dz.Z))]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
