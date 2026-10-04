import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen

/-!
# `PolyZonotope.polygonRound`

One round of `polygon`'s loop: every piece the verdict `pick` selects is replaced by its two
halves along the longest generator, the others are kept.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.polygonRound (pick : PolyZonotope (Vec ℝ 2) → Bool)
    (L : List (PolyZonotope (Vec ℝ 2))) : List (PolyZonotope (Vec ℝ 2)) :=
  L.flatMap fun q => if pick q then [q.splitLongestGen.1, q.splitLongestGen.2] else [q]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
