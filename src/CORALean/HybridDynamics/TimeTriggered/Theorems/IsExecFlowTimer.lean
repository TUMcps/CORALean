module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt

@[expose] public section

/-!
# A curve with a running timer extends an execution

In an automaton whose state is `(x, t)` with `ṫ = 1` ([1, Sec. 3.1]), a curve `w` with derivative
`V` on `[0, r]` whose derivative and invariant fit the mode `k` at the timer `τ + u` extends an
execution ending at `(w 0, τ)` by one continuous successor of duration `r`, or by none if `r = 0`.

## Inputs
* `H` – automaton with a clock
* `k` – mode
* `d` – duration so far
* `τ` – clock at the start
* `r` – extension time
* `w` – curve
* `V` – derivative of the curve

## Hypotheses
* `hr` – extension time nonnegative
* `hw` – curve has the derivative on the closed interval
* `hflow` – derivative lies in the flow with rate one
* `hinv` – curve lies in the invariant
* `h` – execution ends at the curve start

## Conclusion
* the execution extends to the curve end

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {M X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Extending an execution by a curve `w` in mode `k`, the timer running at rate one. -/
theorem DiffInclAutomaton.isExec_flow_timer {H : DiffInclAutomaton M (X × ℝ)} {k : M}
    {d τ r : ℝ} {w V : ℝ → X} (hr : 0 ≤ r) (hw : ∀ u ∈ Icc 0 r, HasDerivAt w (V u) u)
    (hflow : ∀ u ∈ Ioo 0 r, (V u, (1 : ℝ)) ∈ H.flow k (w u, τ + u))
    (hinv : ∀ u ∈ Ioo 0 r, (w u, τ + u) ∈ H.inv k) (h : H.IsExec d k (w 0, τ)) : -- --- CONCL ---
    H.IsExec (d + r) k (w r, τ + r) := by -- --- PROOF ---
  rcases hr.eq_or_lt with rfl | hpos
  · simpa using h
  · -- the pair `(w u, τ + u)` has derivative `(V u, 1)`
    have hy : ∀ u ∈ Icc 0 r, HasDerivAt (fun u => (w u, τ + u)) (V u, 1) u := fun u hu =>
      (hw u hu).prodMk
        (by simpa using (hasDerivAt_id u).const_add τ : HasDerivAt (fun δ : ℝ => τ + δ) 1 u)
    have := DiffInclAutomaton.flows_of_hasDerivAt (H := H) (m := k) hpos hy hflow hinv
    simp only [add_zero] at this
    exact h.flow this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
