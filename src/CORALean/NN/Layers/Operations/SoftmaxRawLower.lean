module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.Exp
public import CORALean.NN.Layers.Operations.SumOffUp
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Softmax's raw lower bound

`(1 + ∑_{j≠i} exp(hi j - lo i))⁻¹` with the denominator overestimated and the reciprocal rounded
down, where `step_softmaxExpInRange` licenses `expUp`; zero elsewhere.

## Inputs
* `k` – reduction depth of the exponential
* `I` – box of the layer's input
* `i` – output coordinate

## Output
* raw lower bound of the coordinate's softmax
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `2 ^ k / 2`, each doubling rounded down. -/
@[step_of softmaxRawLower]
def step_expUpLimit : ℕ → 𝕋
  | 0 => half one
  | k + 1 => addDown (step_expUpLimit k) (step_expUpLimit k)

/-- Every term and both additions rounded up. -/
@[step_of softmaxRawLower]
def step_softmaxDenomUp (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  addUp one (sumOffUp i fun j => expUp k (subUp (I.sup j) (I.inf i)))

/-- Whether `subUp (sup j) (inf i)` is at most `step_expUpLimit k` for every `j ≠ i`. -/
@[step_of softmaxRawLower]
def step_softmaxExpInRange (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : Bool :=
  (List.finRange n).all fun j => decide (j = i) ||
    le (subUp (I.sup j) (I.inf i)) (step_expUpLimit k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reciprocal of `step_softmaxDenomUp` rounded down, or zero where `expUp` is not licensed. -/
def softmaxRawLower (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  if step_softmaxExpInRange k I i = true then divDown one (step_softmaxDenomUp k I i) else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
