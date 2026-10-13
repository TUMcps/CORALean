module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# `Zonotope.longestGen`

The index CORA's `splitLongestGen` splits at: `[~,ind] = max(sum(G.^2, 1))`, the first generator
of maximal squared Euclidean length. The choice is a computable `List.argmax` over the generator
indices; only the real arithmetic is noncomputable. `none` when there is no generator, where CORA
splits nothing either.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first generator of `Z` of maximal squared length `Σᵢ G(i,j)²`. -/
noncomputable def Zonotope.longestGen (Z : Zonotope (Vec ℝ n)) : Option (Fin Z.h) :=
  (List.finRange Z.h).argmax (fun j => ∑ i, Z.G j i ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
