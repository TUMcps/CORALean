import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Plus
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ

/-!
# No independent generator survives the exact polynomial activation layer

ℝ-only, as the layer is: `dependent` empties the input's own independent generators before the
fit runs, and the residual box lands in `Interval.polyZonotope`, which is all dependent too, so
the generator count below is the *whole* count.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPoly_enclose_q (P : LayerRelaxation ℝ n m)
    (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).q = 0 := by -- --- PROOF ---
  show (PolyZonotope.plus
      (s.dependent.evalPoly (P.coeffList
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval ℝ n)))
      (Interval.polyZonotope (P.box
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval ℝ n)).nominal)).q = 0
  rw [PolyZonotope.plus_q, PolyZonotope.evalPoly_q, Interval.polyZonotope_q]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
