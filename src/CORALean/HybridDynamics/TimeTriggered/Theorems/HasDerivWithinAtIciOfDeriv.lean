module

public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-!
# A solution of `ẋ = V(x)` on `(0, t)` has the right derivative at `0`

[1, Def. 4] prints the flow condition on the open interval `(0, t)` only, while the
uniqueness theorems of ODEs read the derivative at the left endpoint. For `V` continuous and
`h` differentiable on `[0, t]` with `ḣ = V(h)` inside, `h` has right derivative `V(h u)` at every
`u ∈ [0, t)`: at `0` the derivative converges to `V(h 0)` and Mathlib's extension lemma applies.

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

open Set Filter Topology

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The right derivative of a solution on `[0, t)`, the left endpoint included. -/
theorem hasDerivWithinAt_Ici_of_deriv_eq {V : X → X} (hV : Continuous V) {h : ℝ → X} {t : ℝ}
    (ht : 0 < t) (hd : DifferentiableOn ℝ h (Icc 0 t))
    (hder : ∀ u ∈ Ioo 0 t, deriv h u = V (h u)) :
    ∀ u ∈ Ico 0 t, HasDerivWithinAt h (V (h u)) (Ici u) u := by -- --- PROOF ---
  intro u hu
  rcases hu.1.eq_or_lt with rfl | hpos
  · -- at `0` the derivative converges to `V (h 0)` from the right
    have hc : ContinuousWithinAt h (Ioo 0 t) 0 :=
      (hd.continuousOn 0 ⟨le_rfl, ht.le⟩).mono Ioo_subset_Icc_self
    have hlim : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT ht]; exact hc
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (hd.mono Ioo_subset_Icc_self) hc
      (Ioo_mem_nhdsGT ht) ?_
    refine (((hV.tendsto (h 0)).comp hlim)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with v hv using (hder v hv).symm
  · exact ((hd.differentiableAt (Icc_mem_nhds hpos hu.2)).hasDerivAt.congr_deriv
      (hder u ⟨hpos, hu.2⟩)).hasDerivWithinAt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
