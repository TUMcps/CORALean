module

public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ContSet/Zonotope/Real/Complexity/Space`: small declarations

One section per operation, its exact statement and `O` corollary together, at most
five code lines each; alphabetical, after the sections each one uses (CONTRIBUTING,
"Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

open Matrix

variable {n m : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===================================  `Zonotope.linComb_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `linComb`'s generator count: the two operands' plus the one fresh generator
that ties them together at the interpolating point. `rfl`, since
`Operations/LinComb.lean` states `h` directly in the structure instance. -/
theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope α) : (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl


-- ===================================  `Zonotope.mtimes_h`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimes` is `map` at `A *ᵥ ·`: the generator count carries over exactly, since
a linear image reuses the same index type `Fin h` rather than growing or
shrinking it. `rfl`, since `Operations/Mtimes.lean` states `h` directly. -/
theorem Zonotope.mtimes_h (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimes M Z).h = Z.h := rfl


-- ====================================  `Zonotope.plus_h`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

omit [Module ℝ α] in
/-- `plus`'s generator count: the two operands' concatenated, with nothing
absorbed and nothing bounded. `rfl`, since `Operations/Plus.lean` states `h`
directly in the structure instance. -/
theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope α) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl

end


section

variable {m n : ℕ}


-- ==============================  `Zonotope.mtimesMatZonotope_h`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimesMatZonotope` is `bilin` at `Matrix.mulVecBilin`, so its count is
`bilin`'s: quadratic in the two operands' generator counts. `rfl`, by unfolding
the definition rather than restating `bilin_h`. -/
theorem Zonotope.mtimesMatZonotope_h (M : Zonotope (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimesMatZonotope M Z).h = M.h + Z.h + M.h * Z.h := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
