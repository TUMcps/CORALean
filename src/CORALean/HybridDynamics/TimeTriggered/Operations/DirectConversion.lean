import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# The direct time-triggered conversion

[1, Sec. 3.1]'s `H_tt`: the space-triggered transition of `spaceTriggered` is removed, a mode
`m_either = 1` with flow `f_either ⊇ f₁ ∪ f₂` is put between `m₁ = 0` and `m₂ = 2`, and a time
variable `t` with `ṫ = 1` is added, reset to `0` on entering each mode. The guards are
`t = t₁` and `t = t₂`, the invariants `t ≤ t₁` and `t ≤ t₂`; `m₂` keeps the whole space as its
invariant. `t₁`, `t₂` are parameters here, their selection being `FirstDwell`, `SecondDwell`;
it is the `H_tt` of [1, Lemma 1].

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

/-- `H_tt` of [1, Sec. 3.1]: the state is `(x, t)`. -/
def DiffInclAutomaton.directConversion (I : Set X) (f₁ f₂ : X → X) (fe : X → Set X)
    (t₁ t₂ : ℝ) : DiffInclAutomaton (Fin 3) (X × ℝ) where
  init m := if m = 0 then I ×ˢ {0} else ∅
  flow m p := (if m = 0 then {f₁ p.1} else if m = 1 then fe p.1 else {f₂ p.1}) ×ˢ {1}
  inv m := if m = 0 then Set.univ ×ˢ Set.Iic t₁ else
    if m = 1 then Set.univ ×ˢ Set.Iic t₂ else Set.univ
  trans := {⟨0, {p | p.2 = t₁}, fun p => (p.1, 0), 1⟩, ⟨1, {p | p.2 = t₂}, fun p => (p.1, 0), 2⟩}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
