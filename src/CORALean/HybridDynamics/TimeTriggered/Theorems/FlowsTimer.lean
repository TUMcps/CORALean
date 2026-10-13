module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

@[expose] public section

/-!
# A flow carries a time variable along

[1, Sec. 3.1] adds a time variable `t` with `ṫ = 1` in every mode. A continuous successor of
one automaton is one of another whose state is `(x, t)`, the time variable counting the dwell,
when the other's flow contains `ẋ ∈ f(x)` with `ṫ = 1` and its invariant holds while the
timer is at most `c`.

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

variable {M M' X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A continuous successor of `H` is one of `H'` with the timer `τ` running at rate one. -/
theorem DiffInclAutomaton.flows_timer {H : DiffInclAutomaton M X}
    {H' : DiffInclAutomaton M' (X × ℝ)} {m : M} {k : M'} {x x' : X} {t τ c : ℝ}
    (h : H.Flows m x t x') (hflow : ∀ y τ', ∀ v ∈ H.flow m y, (v, (1 : ℝ)) ∈ H'.flow k (y, τ'))
    (hinv : ∀ y ∈ H.inv m, ∀ τ' ≤ c, (y, τ') ∈ H'.inv k) (hc : τ + t ≤ c) :
    H'.Flows k (x, τ) t (x', τ + t) := by -- --- PROOF ---
  obtain ⟨ht, g, hd, h0, htt, hg⟩ := h
  refine ⟨ht, fun δ => (g δ, τ + δ), DifferentiableOn.prodMk hd (by fun_prop),
    by simp [h0], by simp [htt], fun δ hδ => ?_⟩
  obtain ⟨hi, hfl⟩ := hg δ hδ
  -- the derivative of the pair is the pair of the derivatives
  have hda : HasDerivAt g (deriv g δ) δ :=
    (hd.differentiableAt (Icc_mem_nhds hδ.1 hδ.2)).hasDerivAt
  have hτ : HasDerivAt (fun δ : ℝ => τ + δ) 1 δ := by
    simpa using (hasDerivAt_id δ).const_add τ
  have hp := HasDerivAt.prodMk hda hτ
  exact ⟨hinv _ hi _ (by linarith [hδ.2]), by rw [hp.deriv]; exact hflow _ _ _ hfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
