module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.basicPoint`

Choose some of the inequality rows and demand they hold with equality; the
equalities hold anyway. If exactly one point does that, this is it, and
otherwise the choice names nothing and the value is junk — which callers filter
by feasibility rather than by inspecting it.

No matrix is inverted and no basis is extracted. Uniqueness is stated rather
than computed, which is what makes the argument short: a second solution differs
from the first by a direction every chosen row and every equality fails to see,
and at an extreme point there is no such direction.

Noncomputable, and unavoidably so at this layer — whether two reals are equal is
not decidable, so which rows are tight is not either.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.basicPoint (P : HPolytope (Vec ℝ n)) (σ : Fin P.m → Bool) :
    Vec ℝ n :=
  if h : ∃! y : Vec ℝ n, (∀ i, σ i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i then
    h.choose
  else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
