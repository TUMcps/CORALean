module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.bordered`

A float vertex matrix `V` (`n × k`) with a row of ones appended: `[V; 1ᵀ]`, `(n + 1) × k`. Its
right inverse reaches, besides the points near the vertices' mean, the weights' sum, which is
what a convex combination fixes at one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.bordered (P : VPolytope (Vec 𝕋 n)) : Mat 𝕋 (n + 1) P.k := fun i j =>
  if h : i.val < n then P.V j ⟨i.val, h⟩ else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
