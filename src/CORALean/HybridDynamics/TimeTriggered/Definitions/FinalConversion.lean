module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# The combined scaled time-triggered transformation

[1, Sec. 3.3]'s `H_final`. Step 1 is `directConversion`: modes `m₁ = 0`, `m_either = 2`,
`m₂ = 3`, a timer reset on entering each. Step 2 applies the dynamics scaling of [1, Sec. 3.2]
to `m₁` with `t_begin = t₁` and `g(x) = (b - a·x) / ‖a‖`, the distance to the guard
`G = {x | a·x = b}`: a mode `m_scaling = 1` with the flow `ẋ = g(x) f₁(x)` is entered at `t = t₁`
and left at `t = t_scaling`. Step 3 goes from `m_scaling` straight to `m_either`, `m₁'` being
deleted. The invariants are `t ≤ t₁`, `t ≤ t_scaling`, `t ≤ t₂` and, for `m₂`, the whole space.
It is the `H_final` of [1, Cor. 1] and [1, Thm. 1].

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

/-- `H_final` of [1, Sec. 3.3]: the state is `(x, t)`. -/
noncomputable def DiffInclAutomaton.finalConversion (I : Set X) (f₁ f₂ : X → X)
    (fe : X → Set X) (a : X) (b : ℝ) (t₁ t₂ tScaling : ℝ) : DiffInclAutomaton (Fin 4) (X × ℝ) :=
  -- step 2: the scaling function, the distance from `x` to the guard `{x | a·x = b}`
  let g : X → ℝ := fun x => (b - inner ℝ a x) / ‖a‖
  -- steps 1 and 3: the time-triggered modes, with `m_scaling` between `m₁` and `m_either`
  { init := fun m => if m = 0 then I ×ˢ {0} else ∅
    flow := fun m p => (if m = 0 then {f₁ p.1} else if m = 1 then {g p.1 • f₁ p.1} else
      if m = 2 then fe p.1 else {f₂ p.1}) ×ˢ {1}
    inv := fun m => if m = 0 then Set.univ ×ˢ Set.Iic t₁ else
      if m = 1 then Set.univ ×ˢ Set.Iic tScaling else
      if m = 2 then Set.univ ×ˢ Set.Iic t₂ else Set.univ
    trans := {⟨0, {p | p.2 = t₁}, fun p => (p.1, 0), 1⟩,
      ⟨1, {p | p.2 = tScaling}, fun p => (p.1, 0), 2⟩, ⟨2, {p | p.2 = t₂}, fun p => (p.1, 0), 3⟩} }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
