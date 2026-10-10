import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.bordered`

A float vertex matrix `V` (`n × k`) with a row of ones appended: `[V; 1ᵀ]`, `(n + 1) × k`. Its
right inverse reaches, besides the points near the vertices' mean, the weights' sum, which is
what a convex combination fixes at one.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.bordered (P : VPolytope 𝕋 n) : Mat 𝕋 (n + 1) P.k := fun i j =>
  if h : i.val < n then P.V j ⟨i.val, h⟩ else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
