import CORALean.ContSet.HPolytope.Real.Operations.And

/-!
# `HPolytope.and`'s counts

Both rows lists concatenate, inequalities and equalities alike, so an
intersection costs nothing and loses nothing. `rfl` against the structure
instance in `Operations/And.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.and_m (P₁ P₂ : HPolytope α) : (P₁.and P₂).m = P₁.m + P₂.m := rfl

theorem HPolytope.and_me (P₁ P₂ : HPolytope α) : (P₁.and P₂).me = P₁.me + P₂.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
