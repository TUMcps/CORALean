module

public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ContSet/HPolytope/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===============================  `HPolytope.intersection_me`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `me` count of `intersection`'s result. -/
theorem HPolytope.intersection_me (P₁ P₂ : HPolytope α) :
    (P₁.intersection P₂).me = P₁.me + P₂.me := rfl


-- ================================  `HPolytope.minkDiffOf_me`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `me` count of `minkDiffOf`'s result. -/
theorem HPolytope.minkDiffOf_me (P : HPolytope α) (T : Set α)
    (u : ∀ i, SupportBound T (P.A i)) : (P.minkDiffOf T u).me = P.me := rfl

end

section

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

variable {q : ℕ} {P : HPolytope α}


-- =================================  `HPolytope.mtimesOf_me`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `me` count of `mtimesOf`'s result. -/
theorem HPolytope.mtimesOf_me (M : α →ₗ[ℝ] β) (Aq : Fin q → (β →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) :
    (HPolytope.mtimesOf M Aq u).me = 0 := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
