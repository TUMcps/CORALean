module

public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.Kleene.Instances
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# The negation of three-valued signals is antitone

If `Λ ⊑ₜ Λ'` at every time `t ≥ 0`, then `¬Λ' ⊑ₜ ¬Λ` there: `¬` on `U₁`-signals is antitone
([1, Lemma 3]).

## Inputs
* `s` – three-valued signal
* `s'` – second three-valued signal

## Hypotheses
* `hs` – the first signal is valid
* `hs'` – the second signal is valid
* `h` – the first is below the second at all times

## Conclusion
* the negations are in reverse order at all times

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.not_anti (s s' : KleeneSignal ℝ) (hs : s.IsValid) (hs' : s'.IsValid)
    (h : ∀ t : ℝ, 0 ≤ t → s.at t ≤ s'.at t) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t → s'.not.at t ≤ s.not.at t := by -- --- PROOF ---
  intro t ht
  rw [KleeneSignal.at_not s hs, KleeneSignal.at_not s' hs']
  have := h t ht
  revert this
  cases s.at t <;> cases s'.at t <;> simp [Kleene.not, Kleene.le_iff_code, Kleene.code]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
