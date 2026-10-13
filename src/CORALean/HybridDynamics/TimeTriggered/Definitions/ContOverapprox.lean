import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# Time-bounded continuous overapproximation

[1, Def. 8]: `H'` with time bound `T'` is a time-bounded continuous overapproximation of `H`
with time bound `T` when `Reach≤T(H) ⊆ Reach≤T'(H')`, the variables exclusive to `H'` projected
away before the comparison. `π` is the projection onto the variables of `H`. [1, Lemma 1],
[1, Lemma 2] and [1, Cor. 1] are statements of it.

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

variable {M M' X X' : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup X']
  [NormedSpace ℝ X']


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `H'` with time bound `T'` overapproximates `H` with time bound `T`, [1, Def. 8]. -/
def DiffInclAutomaton.ContOverapprox (H : DiffInclAutomaton M X) (T : ℝ)
    (H' : DiffInclAutomaton M' X') (π : X' → X) (T' : ℝ) : Prop :=
  H.reachLE T ⊆ π '' H'.reachLE T'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
