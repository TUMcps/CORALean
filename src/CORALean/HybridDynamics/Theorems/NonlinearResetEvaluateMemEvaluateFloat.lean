module

public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluateFloat
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate

@[expose] public section

/-!
# The real reset value lies in the float box

For a float model that encloses the reset, `evaluate` at any point of the boxes lies in the box
`evaluateFloat` returns. An outer statement; the box is not the value.

## Inputs
* `r` – reset
* `fm` – float reset model
* `X` – box of states
* `U` – box of inputs
* `x` – state
* `u` – input vector

## Hypotheses
* `h` – the model encloses the reset
* `hx` – state lies in its box
* `hu` – input lies in its box

## Conclusion
* reset value lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.evaluate_mem_evaluateFloat (r : NonlinearReset n m p)
    {fm : NonlinearReset.FloatModel 𝕋 n m p} (h : fm.Encloses r) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) {x : Vec ℝ n} (hx : x ∈ construct X) {u : Vec ℝ m}
    (hu : u ∈ construct U) : r.evaluate x u ∈ construct (fm.evaluateFloat X U) :=
  h.f_mem X U x hx u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
