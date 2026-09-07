import CORALean.ContSet.HPolytope.Real.Operations.Intersection

/-!
# `HPolytope.intersection`'s counts

Both rows lists concatenate, inequalities and equalities alike, so an
intersection costs nothing and loses nothing. `rfl` against the structure
instance in `Operations/Intersection.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_m (P₁ P₂ : HPolytope α) : (P₁.intersection P₂).m = P₁.m + P₂.m := rfl

theorem HPolytope.intersection_me (P₁ P₂ : HPolytope α) :
    (P₁.intersection P₂).me = P₁.me + P₂.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
