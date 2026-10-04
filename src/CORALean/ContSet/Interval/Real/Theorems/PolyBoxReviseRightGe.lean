import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseRight
import CORALean.ContSet.Interval.Real.Definitions.RootBound
import Mathlib.Topology.Order.IntermediateValue

/-!
# The right bound keeps every solution

The mirror image of `Interval.polyBoxReviseLeft_le`, for [1, Sec. 3 (three cases)]'s
"symmetric process": every `x ∈ [x̲, x̅]` with `g̲(x) ≤ 0 ≤ g̅(x)` lies left of the new right
bound, by the intermediate value theorem on `[x, x̅]`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.le_polyBoxReviseRight {gLo gHi : ℝ → ℝ} {root : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {xl xu x : ℝ} (hroot : Interval.IsRightRootBound root)
    (hLo : ContinuousOn gLo (Set.Icc xl xu)) (hHi : ContinuousOn gHi (Set.Icc xl xu))
    (hx : x ∈ Set.Icc xl xu) (hxLo : gLo x ≤ 0) (hxHi : 0 ≤ gHi x) :
    x ≤ Interval.polyBoxReviseRight gLo gHi root xl xu := by -- --- PROOF ---
  have hsub : Set.Icc x xu ⊆ Set.Icc xl xu := Set.Icc_subset_Icc hx.1 le_rfl
  unfold Interval.polyBoxReviseRight
  split_ifs with h1 h2
  · exact hx.2
  · -- case 2: `g̲(x) ≤ 0 < g̲(x̅)`, a zero of `g̲` in `[x, x̅]`
    by_contra hlt
    obtain ⟨z, hz, hz0⟩ : 0 ∈ gLo '' Set.Icc x xu :=
      intermediate_value_Icc hx.2 (hLo.mono hsub) ⟨hxLo, h2.le⟩
    exact hroot gLo xl xu hLo z (hsub hz) (lt_of_lt_of_le (not_le.mp hlt) hz.1) hz0
  · -- case 3: `g̅(x̅) < 0 ≤ g̅(x)`, a zero of `g̅` in `[x, x̅]`
    have h3 : gHi xu < 0 := by
      by_contra h
      exact h1 ⟨not_lt.mp h2, not_lt.mp h⟩
    by_contra hlt
    obtain ⟨z, hz, hz0⟩ : 0 ∈ gHi '' Set.Icc x xu :=
      intermediate_value_Icc' hx.2 (hHi.mono hsub) ⟨h3.le, hxHi⟩
    exact hroot gHi xl xu hHi z (hsub hz) (lt_of_lt_of_le (not_le.mp hlt) hz.1) hz0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
