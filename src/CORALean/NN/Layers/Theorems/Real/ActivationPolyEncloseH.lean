import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Plus
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ

/-!
# The exact polynomial activation layer's generator count

ℝ-only, as the layer is. [1, Lemma 4.3]: a closed form in the input's own `s.h + s.q` and the
layer's shared degree `m` — `Alg. 1` line 9's padding — with nothing of the fits beyond `m`
reaching it, and `n` more from the residual box.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
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

theorem Layer.activationPoly_enclose_h (P : LayerRelaxation ℝ n m)
    (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).h = (s.h + s.q + 1) *
      (∑ i ∈ Finset.range (m + 1), (s.h + s.q + 1) ^ i) + n := by -- --- PROOF ---
  show (PolyZonotope.plus
      (s.dependent.evalPoly (P.coeffList
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))))
      (Interval.polyZonotope (P.box
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).nominal)).h = _
  have hlen :
      (P.coeffList (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).length = m + 1 :=
    List.length_ofFn
  rw [PolyZonotope.plus_h, PolyZonotope.evalPoly_h, PolyZonotope.dependent_h, hlen,
    Interval.polyZonotope_h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
