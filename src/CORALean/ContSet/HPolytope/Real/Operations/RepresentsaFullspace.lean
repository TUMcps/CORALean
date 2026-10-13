module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.representsaFullspace`

CORA's `representsa_(P, 'fullspace')` on an H-representation: "all constraints must be trivially
fulfilled, that is, `A x ≤ a`, `a ≥ 0`, and `Ae x = 0`" — every inequality row is `0 ≤ b` with
`b ≥ 0` (CORA: `b > 0` or `withinTol(b, 0)`), every equality row is `0 = 0`. The tolerance is `0`
here. `Theorems.RepresentsaFullspaceIff` says this is the whole space.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.representsaFullspace (P : HPolytope α) : Prop :=
  (∀ i, P.A i = 0 ∧ 0 ≤ P.b i) ∧ ∀ r, P.Ae r = 0 ∧ P.be r = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
