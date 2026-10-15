module

public import CORALean.ContSet.HPolytope.Real.Operations.Mtimes

@[expose] public section

/-!
# `HPolytope.mtimesOf`'s counts

`mtimesOf` is `ofBounds` at the caller's directions: the row count is `q`, the
directions' own count, not a function of the operand's — and the equality
count is fixed at zero, an image under an arbitrary linear map bounding
nothing exactly. `rfl` against `Operations/OfBounds.lean`, which `mtimesOf`
does not otherwise touch.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

variable {q : ℕ} {P : HPolytope α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `m` count of `mtimesOf`'s result. -/
theorem HPolytope.mtimesOf_m (M : α →ₗ[ℝ] β) (Aq : Fin q → (β →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) :
    (HPolytope.mtimesOf M Aq u).m = q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
