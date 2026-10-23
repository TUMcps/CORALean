module

public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal
public import CORALean.Specification.TentativeKleeneSignal.Operations.At

@[expose] public section

/-!
# The value of a tentative signal

The value at a time is read off the two parts: `True` iff only `canBeTrue` holds, `False` iff only
`canBeFalse`, `Unknown` iff both, `Inconclusive` iff neither.

## Inputs
* `T` – time type
* `s` – tentative signal
* `t` – time

## Hypotheses
* none

## Conclusion
* each value is read off the two Boolean parts
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.at_eq_iff {T : Type} [LinearOrder T] (s : TentativeKleeneSignal T)
    (t : T) : -- --- CONCL ---
    (s.at t = .tt ↔ s.canBeTrue.at t = true ∧ s.canBeFalse.at t = false) ∧
      (s.at t = .ff ↔ s.canBeTrue.at t = false ∧ s.canBeFalse.at t = true) ∧
      (s.at t = .uu ↔ s.canBeTrue.at t = true ∧ s.canBeFalse.at t = true) ∧
      (s.at t = .ii ↔ s.canBeTrue.at t = false ∧ s.canBeFalse.at t = false) := by -- --- PROOF ---
  unfold TentativeKleeneSignal.at
  rcases Bool.eq_false_or_eq_true (s.canBeTrue.at t) with hA | hA <;>
    rcases Bool.eq_false_or_eq_true (s.canBeFalse.at t) with hB | hB <;> simp [hA, hB]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
