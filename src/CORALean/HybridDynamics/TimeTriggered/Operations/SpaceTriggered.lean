module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# The automaton the conversion starts from

[1, Assumption 1, Assumption 2]: two modes `m₁ = 0` and `m₂ = 1` with deterministic flows
`f₁`, `f₂`, all initial states `I` in `m₁`, and one transition `m₁ → m₂`, space-triggered by
the guard `G = {x | a·x = b}` with no reset, the invariant of `m₁` being `a·x ≤ b`. The paper
leaves the invariant of `m₂` open; here it is the whole space. It is the `H` of [1, Lemma 1].

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

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The original automaton `H` of [1, Assumption 1, Assumption 2]. -/
def DiffInclAutomaton.spaceTriggered (I : Set X) (f₁ f₂ : X → X) (a : X) (b : ℝ) :
    DiffInclAutomaton (Fin 2) X where
  init m := if m = 0 then I else ∅
  flow m x := {if m = 0 then f₁ x else f₂ x}
  inv m := if m = 0 then {x | inner ℝ a x ≤ b} else Set.univ
  trans := {⟨0, {x | inner ℝ a x = b}, id, 1⟩}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
