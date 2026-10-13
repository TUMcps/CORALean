import CORALean.ContSet.Ellipsoid.Real.Operations.Plus

/-!
# `Ellipsoid.plus_k`

`plus`'s generator count: the two operands' concatenated into the wider
generator matrix `H = [s₁ G₁ | s₂ G₂]`, exactly as a zonotope's would. `rfl`,
since `Operations/Plus.lean` states `k` directly in the structure instance.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.plus_k (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).k = E₁.k + E₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
