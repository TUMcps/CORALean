module

public import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseLeft
public import CORALean.ContSet.Interval.Real.Definitions.RootBound
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The left bound keeps every solution

[1, Sec. 3 (three cases)] is a contraction, so the point is that it loses no solution: every
`x ∈ [x̲, x̅]` passing the test `g̲(x) ≤ 0 ≤ g̅(x)` lies right of the new bound. In case 2,
`g̲(x̲) > 0 ≥ g̲(x)`, so the continuous `g̲` has a zero in `[x̲, x]` and the root search cannot
pass `x`; case 3 is the same at `g̅`. Continuity of the extremal functions is assumed, as the
paper does for its `hᵢ`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.polyBoxReviseLeft_le {gLo gHi : ℝ → ℝ} {root : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {xl xu x : ℝ} (hroot : Interval.IsLeftRootBound root)
    (hLo : ContinuousOn gLo (Set.Icc xl xu)) (hHi : ContinuousOn gHi (Set.Icc xl xu))
    (hx : x ∈ Set.Icc xl xu) (hxLo : gLo x ≤ 0) (hxHi : 0 ≤ gHi x) :
    Interval.polyBoxReviseLeft gLo gHi root xl xu ≤ x := by -- --- PROOF ---
  have hsub : Set.Icc xl x ⊆ Set.Icc xl xu := Set.Icc_subset_Icc le_rfl hx.2
  unfold Interval.polyBoxReviseLeft
  split_ifs with h1 h2
  · exact hx.1
  · -- case 2: `g̲` changes sign on `[x̲, x]`, so its zero there is not left of the root
    by_contra hlt
    obtain ⟨z, hz, hz0⟩ : 0 ∈ gLo '' Set.Icc xl x :=
      intermediate_value_Icc' hx.1 (hLo.mono hsub) ⟨hxLo, h2.le⟩
    exact hroot gLo xl xu hLo z (hsub hz) (lt_of_le_of_lt hz.2 (not_le.mp hlt)) hz0
  · -- case 3: `g̅(x̲) < 0 ≤ g̅(x)`, the same at `g̅`
    have h3 : gHi xl < 0 := by
      by_contra h
      exact h1 ⟨not_lt.mp h2, not_lt.mp h⟩
    by_contra hlt
    obtain ⟨z, hz, hz0⟩ : 0 ∈ gHi '' Set.Icc xl x :=
      intermediate_value_Icc hx.1 (hHi.mono hsub) ⟨h3.le, hxHi⟩
    exact hroot gHi xl xu hHi z (hsub hz) (lt_of_le_of_lt hz.2 (not_le.mp hlt)) hz0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
