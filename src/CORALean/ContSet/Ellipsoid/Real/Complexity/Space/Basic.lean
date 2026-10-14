module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Complexity/Space`: small declarations

One section per operation, its exact statement and `O` corollary together, at most
five code lines each; alphabetical, after the sections each one uses (CONTRIBUTING,
"Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ===================================  `Ellipsoid.mtimes_k`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimes` sends `G` to `M G`, an `m × k` matrix from an `n × k` one, so the
generator count carries over exactly. `rfl`, since `Operations/Mtimes.lean`
states `k` directly. -/
theorem Ellipsoid.mtimes_k (M : Mat ℝ m n) (E : Ellipsoid n) :
    (Ellipsoid.mtimes M E).k = E.k := rfl


-- ====================================  `Ellipsoid.plus_k`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus`'s generator count: the two operands' concatenated into the wider
generator matrix `H = [s₁ G₁ | s₂ G₂]`, exactly as a zonotope's would. `rfl`,
since `Operations/Plus.lean` states `k` directly in the structure instance. -/
theorem Ellipsoid.plus_k (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).k = E₁.k + E₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
