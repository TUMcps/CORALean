module

public import CORALean.Global.Float.Exp
public import CORALean.Global.StepOf
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# The derivative of the softmax cross-entropy loss, on boxes

CORA's default `lossDer` of `computeFGSMAttack`, `@(t, y) softmax(y) - t`, which CORA.cpp's
`compute_fgsm_attack` takes too. The softmax is CORA.cpp's `Tensor::softmax`: `e = exp(y -
max(y))`, then `e ./ sum(e)`, the sum nested as `sumUp`. On a box every step rounds outward: the
shift is the largest upper end (any shift cancels), each quotient divides by the other end's sum,
and where `expUp`'s licence (an argument at most `1/2`) or a positive lower sum fails the bounds
fall back to `[0, 1]`. At a point and round-to-nearest the two ends are CORA.cpp's value.

## Inputs
* `k` – reduction depth of the exponential
* `T` – box of the targets
* `Y` – box of the outputs

## Output
* box enclosing `softmax(y) - t` for every `t` of `T` and `y` of `Y`
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Softmax shifted by its largest input, on the box `Y`. -/
@[step_of softmaxLossDer]
def step_softmaxShift (k : ℕ) (Y : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 m) :=
  let s := maximumOver Y.sup                                                  -- max(y)
  let licensed := (List.finRange m).all fun j => le (subUp (Y.sup j) s) (half one)
  let eLo := fun i => expDown k (subDown (Y.inf i) s)                         -- exp(y - max(y))
  let eHi := fun i => expUp k (subUp (Y.sup i) s)
  let sumLo := sumDown eLo                                                    -- sum(e)
  let sumHi := sumUp eHi
  ⟨fun i => if licensed then divDown (eLo i) sumHi else zero,                 -- e ./ sum(e)
   fun i => if licensed && ltStrict zero sumLo then divUp (eHi i) sumLo else one⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def softmaxLossDer (k : ℕ) (T Y : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 m) :=
  Interval.minus (step_softmaxShift k Y) T                                    -- softmax(y) - t

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
