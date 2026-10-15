module

public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# What the constructor returns

`finiteSignal(time,value)` returns the signal with these arrays exactly when the checks pass: the
arrays are non-empty and of one length, the times strictly increase and are non-negative, and no
two consecutive values are equal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.mk?_eq_some_iff {T V : Type} [LinearOrder T] [Zero T] [DecidableEq V]
    (time : List T) (value : List V) (s : FiniteSignal T V) :
    FiniteSignal.mk? time value = some s ↔
      s.time = time ∧ s.value = value ∧ s.IsValid := by -- --- PROOF ---
  obtain ⟨a, b⟩ := s
  unfold FiniteSignal.mk?
  split_ifs with h
  · constructor
    · intro hh
      cases hh
      exact ⟨rfl, rfl, h⟩
    · rintro ⟨h1, h2, -⟩
      subst h1 h2
      rfl
  · constructor
    · intro hh; cases hh
    · rintro ⟨h1, h2, hv⟩
      subst h1 h2
      exact absurd hv h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
