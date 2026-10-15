module

public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.DependentP
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.EvalPolyH
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.PlusP
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# No independent generator survives the exact polynomial activation layer

ℝ-only, as the layer is: `dependent` empties the input's own independent generators before the
fit runs, and the residual box lands in `Interval.polyZonotope`, which is all dependent too, so
the generator count below is the *whole* count.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))))
      (Interval.polyZonotope (P.box
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).nominal)).q = 0
  rw [PolyZonotope.plus_q, PolyZonotope.evalPoly_q, Interval.polyZonotope_q]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
