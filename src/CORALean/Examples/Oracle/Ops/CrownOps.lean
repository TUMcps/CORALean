import CORALean.NN.Operations.CrownBackwardBoundFloat
import CORALean.NN.Layers.Operations.CrownReluLines
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec

/-!
# The op `neuralNetwork.backwardBound`: CROWN's backward bound

CORA.cpp's `priv_backward_lower` on a chain of `linear` (`W`, `b`) and `relu` layers, a ReLU given
by the box `[l, u]` of its inputs (the forward pass's record) and, optionally, the optimized lower
slopes `alpha` of its crossing neurons. Each ReLU's lines are `crownReluLines`; every row of `C` on
the outputs gets its lower bound over the input box `|x - x₀| ≤ r` (`x`, `r`). Sound at every
`SoundFloatArithmetic` by `Float.CrownNet.backwardBound_le` and `crownReluLines_holds`, given that
every ReLU's input lies in its box on the input box; at nearest it is CORA.cpp's computation.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* the lower bound of each row, `lower`
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

/-- The layers from the one reading the `n` inputs on, as a chain. -/
private def aux_build (dops : DtypeOps 𝕋) :
    (n : ℕ) → List Json → Except String (Σ k, CrownNet 𝕋 n k)
  | n, [] => pure ⟨n, .nil⟩
  | n, layer :: rest => do
    match ← strField layer "kind" with
    | "linear" =>
      checkFields "backwardBound" layer ["kind", "W", "b"]
      let ⟨m, W⟩ ← parseMatColsFixed dops.readExact n (← field layer "W")
      let b ← parseVecFixed dops.readExact m (← field layer "b")
      let ⟨k, tail⟩ ← aux_build dops m rest
      pure ⟨k, .linear W b tail⟩
    | "relu" =>
      checkFields "backwardBound" layer ["kind", "l", "u", "alpha"]
      let l ← parseVecFixed dops.readExact n (← field layer "l")
      let u ← parseVecFixed dops.readExact n (← field layer "u")
      let alpha : Fin n → Option 𝕋 ← match fieldOpt layer "alpha" with
        | none => pure fun _ => none
        | some aj => do
          let a ← parseVecFixed dops.readExact n aj
          pure fun i => some (a i)
      -- CROWN's lines of each neuron
      let L : Fin n → 𝕋 × 𝕋 × 𝕋 × 𝕋 := fun i => crownReluLines (alpha i) (l i) (u i)
      let ⟨k, tail⟩ ← aux_build dops n rest
      pure ⟨k, .act l u (fun i => (L i).1) (fun i => (L i).2.1) (fun i => (L i).2.2.1)
        (fun i => (L i).2.2.2) tail⟩
    | k => throw s!"backwardBound: a layer's `kind` must be linear or relu, not `{k}`"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CROWN's lower bound of every row of `C` on the network's outputs, over the input box. -/
def crownBackwardBoundOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "backwardBound" req ["layers", "x", "r", "C"]
  let ⟨n, x₀⟩ ← parseVecDyn dops.readExact (← field req "x")
  let r ← parseVecFixed dops.readExact n (← field req "r")
  let ⟨k, net⟩ ← aux_build dops n (← arrField req "layers").toList
  let ⟨p, C⟩ ← parseMatColsFixed dops.readExact k (← field req "C")
  pure [("lower", printVec dops.showExact fun (q : Fin p) => net.backwardBound (C q) x₀ r)]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
