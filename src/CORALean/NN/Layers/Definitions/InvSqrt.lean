module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# The inverse square root, clamped at the degree bound the self-loop gives

CORA's `nnInvSqrtRootLayer` and [1, Lemma 2]: a graph convolutional network normalises by
`D̃⁻ᐟ² Ã D̃⁻ᐟ²`, `D̃` the degree matrix of `Ã = A + I`. The self-loop puts every degree at `1` or
above, so `x ↦ x^(-1/2)` is only ever evaluated there — which makes `invSqrt` total: it clamps
at `1`, and the clamp costs nothing exactly because `1` is the bound already guaranteed. What a
graph network's normalisation means, over ℝ; `InvSqrtRelaxation` encloses it.

## Inputs
* `x` – real number to transform

## Output
* inverse square root of the argument, clamped below at one

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inverse square root, clamped below at the degree bound `1` the self-loop guarantees. -/
noncomputable def invSqrt (x : ℝ) : ℝ := (Real.sqrt (max x 1))⁻¹

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
