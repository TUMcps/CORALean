module

public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# The first dwell time of the conversion

[1, Sec. 3.1, step 4] selects `t₁` as the duration up to which "every finite execution has an
end state in mode `m₁`". Read strictly, `d < t₁`, which is the weaker hypothesis and all the
proof of [1, Lemma 1] uses; the paper says "minimum", which would make `t₁` zero. [1, Cor. 1]
and [1, Thm. 1] take it as a hypothesis.

## Inputs
* `H` – two-mode automaton
* `t₁` – candidate dwell time

## Output
* every execution shorter than `t₁` is in the first mode

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modelling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every execution of duration below `t₁` ends in mode `m₁ = 0`. -/
def DiffInclAutomaton.FirstDwell (H : DiffInclAutomaton (Fin 2) X) (t₁ : ℝ) : Prop :=
  ∀ d, d < t₁ → ∀ m x, H.IsExec d m x → m = 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
