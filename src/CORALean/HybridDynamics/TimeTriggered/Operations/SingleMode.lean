import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# A single-mode automaton

[1, Sec. 3.2]'s `H_single`: one mode with the deterministic dynamics `ẋ = f(x)`, the initial
states `I`, no transitions and no invariant; the `H_single` of [1, Lemma 2].

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `H_single` of [1, Sec. 3.2]. -/
def DiffInclAutomaton.singleMode (I : Set X) (f : X → X) : DiffInclAutomaton Unit X where
  init _ := I
  flow _ x := {f x}
  inv _ := Set.univ
  trans := ∅

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
