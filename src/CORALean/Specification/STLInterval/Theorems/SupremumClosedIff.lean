module

public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields

@[expose] public section

/-!
# `supremum` says whether the supremum is a time

The flag `supremum` returns holds iff the supremum is itself one of the times.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the supremum is closed iff a time of the interval attains it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `isMax` holds iff the supremum is attained by a time of the interval. -/
theorem STLInterval.supremum_closed_iff (I : STLInterval 𝕋) (hI : I ≠ .empty) : -- --- CONCL ---
    I.supremum.closed = true ↔
      ∃ t ∈ I.set, I.supremum.value.map STLInterval.toEReal =
        some (t : EReal) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    show rc = true ↔ ∃ t ∈ rawSet (toReal l : ℝ) (toEReal u) lc rc,
      some (toEReal u) = some (t : EReal)
    cases u with
    | top =>
      -- an infinite upper end is open and no time
      simp only [b rfl, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro t _ e
      simp at e
    | coe y =>
      constructor
      · -- the upper bound itself is a time of the interval
        intro hc
        refine ⟨toReal y, ⟨?_, Or.inr ⟨hc, rfl⟩⟩, rfl⟩
        refine rawSet_lower_of_ge ?_ hx.1
        rcases hx.2 with h | ⟨_, h⟩
        · exact (EReal.coe_lt_coe_iff.1 h).le
        · exact (EReal.coe_eq_coe_iff.1 h).le
      · rintro ⟨t, ⟨_, h | ⟨hc, _⟩⟩, e⟩
        · exact absurd (Option.some.inj e ▸ h) (lt_irrefl _)
        · exact hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
