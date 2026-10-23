module

public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# The constructor denotes its bounds

`stlInterval(lb,ub,lc,rc)` denotes the times between `lb` and `ub`, each end in when its
flag is set: forcing an infinite bound open changes no real time, and the empty cases are exactly
the empty set.

## Inputs
* `lb` – lower bound
* `ub` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `hlb` – the lower bound is nonnegative

## Conclusion
* the constructor denotes the set between its bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_stlInterval [ExactLe 𝕋] (lb : 𝕋) (ub : WithTop 𝕋) (lc rc : Bool)
    (hlb : 0 ≤ toReal lb) : -- --- CONCL ---
    (STLInterval.stlInterval lb ub lc rc hlb).set =
      STLInterval.rawSet (toReal lb : ℝ) (STLInterval.toEReal ub) lc rc := by -- --- PROOF ---
  unfold STLInterval.stlInterval
  cases ub with
  | top =>
    -- an infinite upper end is open, which leaves the denoted reals alone
    dsimp only
    rw [dif_pos (Or.inl (by simp [EReal.coe_lt_top]))]
    ext t
    simp [STLInterval.set, STLInterval.rawSet, EReal.coe_lt_top]
  | coe x =>
    dsimp only
    split_ifs with h
    · rfl
    · -- no real time fits between the bounds
      simp only [STLInterval.toEReal_coe] at h
      ext t
      simp only [STLInterval.set, Set.mem_empty_iff_false, STLInterval.rawSet, Set.mem_setOf_eq,
        STLInterval.toEReal_coe,
        false_iff]
      rintro ⟨h1 | ⟨hc, e1⟩, h2 | ⟨hr', e2⟩⟩
      · exact h (Or.inl (h1.trans h2))
      · exact h (Or.inl (e2 ▸ h1))
      · exact h (Or.inl (e1 ▸ h2))
      · exact h (Or.inr ⟨e1.trans e2, hc, hr'⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
