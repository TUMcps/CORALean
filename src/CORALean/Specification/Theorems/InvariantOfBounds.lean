module

public import CORALean.Specification.Specification
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# Bounds certify that an invariant is stayed inside

`Containment.lean` at `Specification.invariant` rather than `Specification.safeSet`: the two
kinds are checked by the identical test (`Specification.holds_invariant`), so the same bound
per halfspace direction discharges either.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_invariant_of_bounds {ι : Type} (c : ι → α →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (u : ∀ i, SupportBound O (c i)) (h : ∀ i, (u i).val ≤ d i) :
    (Specification.invariant {x | ∀ i, c i x ≤ d i}).Holds O :=
  fun _ hx i => le_trans ((u i).le _ hx) (h i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
