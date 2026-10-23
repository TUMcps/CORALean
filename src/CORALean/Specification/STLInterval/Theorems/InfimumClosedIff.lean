module

public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe

@[expose] public section

/-!
# `infimum` says whether the infimum is a time

The flag `infimum` returns holds iff the infimum is itself one of the times.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the infimum is closed iff a time of the interval attains it
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

/-- `isMin` holds iff the infimum is attained by a time of the interval. -/
theorem STLInterval.infimum_closed_iff (I : STLInterval 𝕋) (hI : I ≠ .empty) : -- --- CONCL ---
    I.infimum.closed = true ↔
      ∃ t ∈ I.set, I.infimum.value.map STLInterval.toEReal = some (t : EReal) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    show lc = true ↔ ∃ t ∈ rawSet (toReal l : ℝ) (toEReal u) lc rc,
      some ((toReal l : ℝ) : EReal) = some (t : EReal)
    constructor
    · -- the lower bound itself is a time of the interval
      intro hc
      refine ⟨toReal l, ⟨Or.inr ⟨hc, rfl⟩, ?_⟩, rfl⟩
      refine rawSet_upper_of_le ?_ hx.2
      rcases hx.1 with h | ⟨_, h⟩
      · exact (EReal.coe_lt_coe_iff.1 h).le
      · exact (EReal.coe_eq_coe_iff.1 h).le
    · rintro ⟨t, ⟨h | ⟨hc, _⟩, _⟩, e⟩
      · exact absurd (Option.some.inj e ▸ h) (lt_irrefl _)
      · exact hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
