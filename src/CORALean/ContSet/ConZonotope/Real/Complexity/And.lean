import CORALean.ContSet.ConZonotope.Real.Operations.And

/-!
# `ConZonotope.and`'s counts

`and`'s generator count concatenates, as `plus`'s does. The inequality count
concatenates too, `comap` and `and` costing nothing beyond what each operand's
`P` already had; the equality count carries one further block, `n` rows
pinning the two generator blocks together coordinate by coordinate — the one
constraint list `and` builds beyond what `plus` needs. `rfl` against the
structure instance in `Operations/And.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.and_h (C₁ C₂ : ConZonotope (Vec ℝ n)) : (C₁.and C₂).h = C₁.h + C₂.h := rfl

theorem ConZonotope.and_P_m (C₁ C₂ : ConZonotope (Vec ℝ n)) :
    (C₁.and C₂).P.m = C₁.P.m + C₂.P.m := rfl

theorem ConZonotope.and_P_me (C₁ C₂ : ConZonotope (Vec ℝ n)) :
    (C₁.and C₂).P.me = C₁.P.me + C₂.P.me + n := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
