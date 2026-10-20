module

public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# The time-bounded overapproximation error

[1, Def. 9]: the error `sup_{x' ∈ Reach≤T'(H')} d_{Reach≤T(H)}(x')` is at most `e` when every
`x'` is within `e` of `Reach≤T(H)`, `d_S(x) = inf {‖x - x'‖ | x' ∈ S}`. The supremum is not
formed: "the error is below `δ`" is `∃ e < δ, OverapproxErrorLE … e`, and "zero error" is
`OverapproxErrorLE … 0`. The distance is an extended one, so an empty `Reach≤T(H)` is at
infinite distance. [1, Lemma 2] and [1, Thm. 1] are statements about it.

## Inputs
* `H` – original automaton
* `T` – time bound
* `H'` – converted automaton
* `π` – projection to the original state
* `T'` – converted time bound
* `e` – error bound

## Output
* every projected state is within the error of the original reach set

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

/-- The error of `H'` against `H` is at most `e`, [1, Def. 9]. -/
def DiffInclAutomaton.OverapproxErrorLE (H : DiffInclAutomaton M X) (T : ℝ)
    (H' : DiffInclAutomaton M' X') (π : X' → X) (T' : ℝ) (e : ENNReal) : Prop :=
  ∀ x' ∈ π '' H'.reachLE T', Metric.infEDist x' (H.reachLE T) ≤ e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
