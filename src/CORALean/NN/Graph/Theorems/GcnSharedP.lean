import CORALean.NN.Graph.Operations.GcnShared

/-!
# `gcnShared` keeps the factor set

`gcnShared` is `bilin` at `matMulBilin`, `[1, Lemma 1]`'s enclosure; `bilin` keeps
`P.p` and `map` keeps `p`, which is what a chain of steps at one graph rests on,
and what the type does not say.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A step keeps the factor set — `bilin` keeps `P.p` and `map` keeps `p` — which
is what a chain of steps at one graph rests on, and what the type does not say. -/
theorem GNN.gcnShared_p (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) :
    (GNN.gcnShared W P H hp).p = P.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
