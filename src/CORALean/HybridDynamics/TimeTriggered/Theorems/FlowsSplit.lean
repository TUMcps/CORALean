import Mathlib.Analysis.Calculus.Deriv.Shift
import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton

/-!
# A continuous successor splits at any interior time

A differentiable `g : [0, t] → X` restricts to `[0, s]` and, shifted, to `[s, t]`, and both
pieces are continuous successors of [1, Def. 4] in the same mode. The mirror of a flow that
crosses a time-triggered guard is built from this.

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

variable {M X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A continuous successor over `t` is one over `s` followed by one over `t - s` ([1, Def. 4]). -/
theorem DiffInclAutomaton.flows_split {H : DiffInclAutomaton M X} {m : M} {x x' : X}
    {t s : ℝ} (h : H.Flows m x t x') (hs : 0 < s) (hst : s < t) :
    ∃ y, H.Flows m x s y ∧ H.Flows m y (t - s) x' := by -- --- PROOF ---
  obtain ⟨_, g, hd, h0, ht, hg⟩ := h
  refine ⟨g s, ⟨hs, g, hd.mono (Set.Icc_subset_Icc le_rfl hst.le), h0, rfl, fun δ hδ => ?_⟩,
    ⟨by linarith, fun δ => g (s + δ), ?_, by simp, by simpa using ht, fun δ hδ => ?_⟩⟩
  · exact hg δ ⟨hδ.1, hδ.2.trans hst⟩
  · -- the shifted piece is the composite of `g` with `δ ↦ s + δ`
    refine hd.comp ((differentiable_id.const_add s).differentiableOn) fun δ hδ => ⟨?_, ?_⟩
    · linarith [hδ.1]
    · linarith [hδ.2]
  · have h1 := hg (s + δ) ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
    exact ⟨h1.1, by rw [deriv_comp_const_add]; exact h1.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
