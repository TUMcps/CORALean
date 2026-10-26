module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# What `withinTolFloat` decides

`withinTolFloat` is `true` exactly when the bounds, read as extended reals, are within the tolerance
read as a real (`IsWithinTol`): two stored values by the exact test, two `inf`s as the same
infinity, and never a stored value against `inf`.

## Inputs
* `tol` – tolerance
* `a` – first bound
* `b` – second bound

## Hypotheses
* none

## Conclusion
* the float test is `IsWithinTol` of the bounds read as extended reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.withinTolFloat_iff (tol : 𝕋) (a b : WithTop 𝕋) : -- --- CONCL ---
    STLInterval.withinTolFloat tol a b = true ↔
      STLInterval.IsWithinTol (toReal tol) (STLInterval.toEReal a)
        (STLInterval.toEReal b) := by -- --- PROOF ---
  rcases a with _ | x <;> rcases b with _ | y
  · -- the same infinity
    simp [STLInterval.withinTolFloat, STLInterval.IsWithinTol]
  · simp [STLInterval.withinTolFloat, STLInterval.IsWithinTol]
  · simp [STLInterval.withinTolFloat, STLInterval.IsWithinTol]
  · -- two stored values: the exact test
    simp only [STLInterval.withinTolFloat, STLInterval.IsWithinTol, ExactLe.withinTol_iff]
    constructor
    · intro h
      exact Or.inl ⟨toReal x, toReal y, rfl, rfl, h⟩
    · rintro (⟨x', y', hx, hy, h⟩ | ⟨-, h | h⟩)
      · rw [STLInterval.toEReal_some, EReal.coe_eq_coe_iff] at hx hy
        rw [hx, hy]
        exact h
      · simp at h
      · simp at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
