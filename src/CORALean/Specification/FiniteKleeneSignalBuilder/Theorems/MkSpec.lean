module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.IsValid
public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Mk
public import CORALean.Specification.FiniteSignal.Theorems.MkSingletonSpec

@[expose] public section

/-!
# What the constructor builds

`finiteKleeneSignalBuilder(dur)` fails exactly for a negative duration. Otherwise both signals are
valid, last `dur` and are false on all of `[0,dur]`: nothing is marked yet, so it represents
the empty predicates.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteKleeneSignalBuilder.mk?_spec (dur : ℝ) :
    (dur < 0 → FiniteKleeneSignalBuilder.mk? dur = none) ∧
    (0 ≤ dur → ∃ b, FiniteKleeneSignalBuilder.mk? dur = some b ∧
      b.Represents dur (fun _ => False) (fun _ => False)) := by -- --- PROOF ---
  obtain ⟨hneg, hpos⟩ := FiniteSignal.mk?_singleton_spec dur false
  refine ⟨fun hd => by simp [FiniteKleeneSignalBuilder.mk?, hneg hd], fun hd => ?_⟩
  -- the constant false signal serves as both
  obtain ⟨s, hs, hv, hdur, hat⟩ := hpos hd
  refine ⟨⟨s, s⟩, by simp [FiniteKleeneSignalBuilder.mk?, hs], ⟨hv, hv, rfl⟩, hdur,
    fun t h0 h1 => ?_⟩
  exact ⟨⟨false, hat t h0 h1, by simp⟩, ⟨false, hat t h0 h1, by simp⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
