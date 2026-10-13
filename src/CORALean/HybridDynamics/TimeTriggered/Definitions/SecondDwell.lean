import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# The second dwell time of the conversion

[1, Sec. 3.1, step 4] selects `t₂` as "the smallest time" such that every finite execution of
duration at least `t₁ + t₂` ends in `m₂`. Only the property is used, not the minimality, and a
smallest `t₂` need not exist: an execution that reaches the guard at duration exactly `t₁ + t₂`
may still be in `m₁`, so the set of admissible `t₂` is open at its lower end. [1, Lemma 1],
[1, Cor. 1] and [1, Thm. 1] take it as a hypothesis.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every execution of duration at least `t₁ + t₂` ends in mode `m₂ = 1`. -/
def DiffInclAutomaton.SecondDwell (H : DiffInclAutomaton (Fin 2) X) (t₁ t₂ : ℝ) : Prop :=
  ∀ d, t₁ + t₂ ≤ d → ∀ m x, H.Exec d m x → m = 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
