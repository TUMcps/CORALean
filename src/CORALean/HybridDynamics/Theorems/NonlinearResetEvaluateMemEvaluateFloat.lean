import CORALean.HybridDynamics.Operations.NonlinearResetEvaluateFloat
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate

/-!
# The real reset value lies in the float box

For a float model that encloses the reset, `evaluate` at any point of the boxes lies in the box
`evaluateFloat` returns. An outer statement; the box is not the value.
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
