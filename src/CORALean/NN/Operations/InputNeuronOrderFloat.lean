module

public import CORALean.NN.Operations.IntervalChainSensitivityFloat
public import CORALean.NN.Operations.SnakeOrder
public import CORALean.NN.Definitions.Basic
public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `getInputNeuronOrder` of a float interval chain
CORA's ranking of the input neurons, in floats: `in-order` and `snake` are the index lists of the
real one, the sensitivity ranking sorts the neurons by the mean absolute sensitivity, stably, with
`IntervalChain.sensitivity` in place of `calcSensitivity`. A float sensitivity is a box, so each
neuron's key is a box too: the sum over the outputs of the absolute entries (and over the channels,
given `inputSize`). The means divide by one positive count, which keeps the order, so the keys are
the sums. The order is committed to only when the key boxes of every two neurons are strictly
separated, which makes the float comparison the real one; otherwise the result is `none`.

## Inputs
* `c` – float interval chain
* `method` – ranking method
* `X` – box of input points
* `inputSize` – image size, if given

## Output
* input neuron indices in ranked order, if the key boxes separate them
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The box of the sum over the outputs of the absolute entries of column `j` of the sensitivity
box, the exact zero for a neuron past the input width. -/
@[step_of IntervalChain.getInputNeuronOrder]
def step_sensitivityKey (S : Interval (Mat 𝕋 m n)) (j : ℕ) : Interval 𝕋 :=
  if hj : j < n then
    ⟨sumDown fun i => maximum zero (maximum (S.inf i ⟨j, hj⟩) (neg (S.sup i ⟨j, hj⟩))),
      sumUp fun i => maximum (neg (S.inf i ⟨j, hj⟩)) (S.sup i ⟨j, hj⟩)⟩
  else ⟨zero, zero⟩

/-- The key box of pixel `p` of `ch` channels of `h * w` neurons: the sum over the channels of the
neurons' keys. -/
@[step_of IntervalChain.getInputNeuronOrder]
def step_channelKey (key : ℕ → Interval 𝕋) (h w ch : ℕ) (p : ℕ) : Interval 𝕋 :=
  ⟨sumDown fun k : Fin ch => (key (p + h * w * k)).inf,
    sumUp fun k : Fin ch => (key (p + h * w * k)).sup⟩

/-- The stable sort of `L` by the key boxes when every two of its neurons are strictly separated:
`a` precedes `b` when the upper end of `a`'s box is at most the lower end of `b`'s. -/
@[step_of IntervalChain.getInputNeuronOrder]
def step_rankByKey (key : ℕ → Interval 𝕋) (L : List ℕ) : Option (List ℕ) :=
  if L.all (fun a => L.all fun b =>
      a == b || le (key a).sup (key b).inf || ltStrict (key b).sup (key a).inf) then
    some (L.mergeSort fun a b => a == b || le (key a).sup (key b).inf)
  else none


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.getInputNeuronOrder (c : IntervalChain 𝕋 n m) (method : InputOrderMethod)
    (X : Interval (Vec 𝕋 n)) (inputSize : Option (ℕ × ℕ × ℕ)) : Option (List ℕ) :=
  match method with
  | .inOrder => some (List.range (match inputSize with | none => n | some (h, w, _) => h * w))
  | .snake =>
    match inputSize with
    | none => some []
    | some (h, w, _) => some (snakeOrder h w fun i j => (i : ℕ) + h * j)
  | .sensitivity =>
    -- the key boxes of the neurons from the sensitivity box
    let key := step_sensitivityKey (c.sensitivity X)
    match inputSize with
    | none => step_rankByKey key (List.range n)
    | some (h, w, ch) => step_rankByKey (step_channelKey key h w ch) (List.range (h * w))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
