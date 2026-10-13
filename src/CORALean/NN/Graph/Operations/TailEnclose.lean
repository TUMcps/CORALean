import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The layers after the global pooling, enclosed one by one

[1, Alg. 1], lines 11 to 14: the standard layers after the pooling, each enclosed by
[1, Prop. 1] (activation) or exactly (linear, [1, Def. 2]), the width `d t` changing from layer to
layer. `tailEnclose` threads a set through the enclosures `f`, `tailEval` is the point through the
layers `g` they enclose. Which layer is which, and what each adds, is what `Alg. 1` fixes and the
theorems about the tail take as hypotheses.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosures `f t` of the layers after the pooling, applied in order. -/
def GNN.tailEnclose : ∀ (T : ℕ) (d : ℕ → ℕ)
    (_ : ∀ t, PolyZonotope (Vec ℝ (d t)) → PolyZonotope (Vec ℝ (d (t + 1)))),
    PolyZonotope (Vec ℝ (d 0)) → PolyZonotope (Vec ℝ (d T))
  | 0, _, _, S => S
  | T + 1, d, f, S => GNN.tailEnclose T (fun t => d (t + 1)) (fun t => f (t + 1)) (f 0 S)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
