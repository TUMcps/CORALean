module

public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# The dynamics scaling transformation

[1, Sec. 3.2]'s `H_scaling`: three copies `m = 0`, `m_scaling = 1`, `m' = 2` of the mode of
`singleMode`, a time variable `t` with `ṫ = 1` reset on entering each, time-triggered
transitions at `t = t_begin` (from `m`) and `t = t_scaling` (from `m_scaling`), and the flow
`ẋ = g(x) f(x)` in `m_scaling`. The invariants are `t ≤ t_begin` and `t ≤ t_scaling`. The paper
asks `g` for "a nonnegative number for every reachable state" and nothing else; the flows are
required Lipschitz by [1, Def. 2], which `g · f` is not made to be. It is the `H_scaling` of
[1, Lemma 2].

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

/-- `H_scaling` of [1, Sec. 3.2]: the state is `(x, t)`. -/
def DiffInclAutomaton.scalingConversion (I : Set X) (f : X → X) (g : X → ℝ)
    (tBegin tScaling : ℝ) : DiffInclAutomaton (Fin 3) (X × ℝ) where
  init m := if m = 0 then I ×ˢ {0} else ∅
  flow m p := (if m = 1 then {g p.1 • f p.1} else {f p.1}) ×ˢ {1}
  inv m := if m = 0 then Set.univ ×ˢ Set.Iic tBegin else
    if m = 1 then Set.univ ×ˢ Set.Iic tScaling else Set.univ
  trans := {⟨0, {p | p.2 = tBegin}, fun p => (p.1, 0), 1⟩,
    ⟨1, {p | p.2 = tScaling}, fun p => (p.1, 0), 2⟩}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
