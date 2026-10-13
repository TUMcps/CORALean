import CORALean.ContSet.Zonotope.Real.Operations.Split
import Mathlib.Data.List.MinMax
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Mul
/-!
# `Zonotope.splitFirstGen`

CORA's `@zonotope/splitFirstGen`: `h(j) = norm(G(:,j)'*G, 1)`, `[~,index] = max(h)` and
`split(Z, index)`. The score `h j = Σₖ |⟨g_j, g_k⟩|` says how strongly generator `j` correlates
with the others, and the first generator of maximal score is chosen by a computable
`List.argmax`. A zonotope with no generator is its own two halves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along the generator of maximal `‖g_jᵀ G‖₁`. -/
noncomputable def Zonotope.splitFirstGen (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  let h := fun j => ∑ k, |Z.G j ⬝ᵥ Z.G k|
  let index := (List.finRange Z.h).argmax h
  match index with
  | some j => Z.split j
  | none => (Z, Z)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
