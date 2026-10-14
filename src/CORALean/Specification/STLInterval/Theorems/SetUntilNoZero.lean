module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.ContainsPointZeroIff
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# The until interval without zero

`untilIntNoZero` of `pointSegmentSignal/until.m` is the until interval with the time `0` removed:
`stlInterval(0,ub,false,rc)` for the supremum `ub` of an interval containing `0`, else the interval
itself. It denotes the times of the interval but `0`, and has lower bound `≥ 0`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- `untilIntNoZero` denotes the times of the until interval except `0`. -/
theorem STLInterval.set_untilNoZero (U U' : STLInterval)
    (hU : ∀ f, U.fieldsOf = some f → 0 ≤ f.lower)
    (hU' : U' = if U.containsPoint 0 0 then
      STLInterval.stlInterval 0 (U.supremum.value.getD 0) false U.supremum.closed else U) :
    U'.set = U.set \ {0} ∧ ∀ f, U'.fieldsOf = some f → 0 ≤ f.lower := by -- --- PROOF ---
  by_cases h : U.containsPoint 0 0
  · -- `0` is in the interval, so the interval starts at `0`, closed
    have h0 := (STLInterval.containsPoint_zero_iff U 0).1 h
    rw [hU', if_pos h]
    cases U with
    | empty => exact absurd h0 (by simp [STLInterval.set])
    | nonempty l u lc rc a b c =>
      have hl := hU _ rfl
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq, EReal.coe_zero] at h0
      have hl0 : l = 0 := by
        rcases h0.1 with h' | ⟨-, h'⟩
        · exact absurd hl (not_le.2 h')
        · exact h'
      have hlc : lc = true := by
        rcases h0.1 with h' | ⟨h', -⟩
        · exact absurd hl (not_le.2 h')
        · exact h'
      refine ⟨?_, fun f hf => ?_⟩
      · -- the sets agree except at `0`
        simp only [STLInterval.supremum, Option.getD_some]
        rw [STLInterval.set_stlInterval]
        ext t
        simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq, Set.mem_sdiff,
          Set.mem_singleton_iff, hl0, hlc]
        constructor
        · rintro ⟨h1 | ⟨h1, -⟩, h2⟩
          · exact ⟨⟨Or.inl h1, h2⟩, fun e => by simp [e] at h1⟩
          · exact absurd h1 (by simp)
        · rintro ⟨⟨h1 | ⟨-, h1⟩, h2⟩, h3⟩
          · exact ⟨Or.inl h1, h2⟩
          · exact absurd (by exact_mod_cast h1.symm) h3
      · simp only [STLInterval.supremum, Option.getD_some] at hf
        rw [STLInterval.lower_stlInterval _ _ _ _ f hf]
  · -- `0` is not in the interval
    have h0 : (0 : ℝ) ∉ U.set := fun h' => h ((STLInterval.containsPoint_zero_iff U 0).2 h')
    rw [hU', if_neg h]
    exact ⟨(Set.sdiff_singleton_eq_self h0).symm, hU⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
