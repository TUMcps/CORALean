module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Bounds.Basic

@[expose] public section

/-!
# A zero exists exactly when `0` lies between the extrema

[1, Sec. 3 (extremal functions)]: with `h̲(x) = min_{y ∈ [Y]} f(x, y)` and `h̅(x)` the maximum,
`0 ∈ [h̲(x), h̅(x)]` is a necessary and sufficient condition for `x` to satisfy `f(x, y) = 0`
for some `y ∈ [Y]`. Sufficiency is the intermediate value theorem, and needs `f(x, ·)`
continuous on `[Y]`, which the paper does not state: without it the condition fails,
`Interval.exists_zero_iff_extrema_counterexample`. `g` is `f(x, ·)`, `S` the box `[Y]`
(convex, hence preconnected), and the minimum and maximum are taken, as the paper's `min`
and `max` say.

## Inputs
* `Y` – domain type
* `S` – domain set
* `g` – function
* `lo` – least value
* `hi` – greatest value

## Hypotheses
* `hS` – `S` preconnected
* `hg` – `g` continuous on `S`
* `hlo` – `lo` is the least value of `g`
* `hhi` – `hi` is the greatest value of `g`

## Conclusion
* a zero exists iff zero lies between the extrema

## References

* [1] [G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". Principles and Practice of Constraint Programming – CP 2010,
      2010.](../../../../../../references/2010/trombettoni-cp-box-consistency.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exists_zero_iff_extrema {Y : Type} [TopologicalSpace Y] {S : Set Y}
    (hS : IsPreconnected S) {g : Y → ℝ} (hg : ContinuousOn g S) {lo hi : ℝ}
    (hlo : IsLeast (g '' S) lo) (hhi : IsGreatest (g '' S) hi) : -- --- CONCL ---
    (∃ y ∈ S, g y = 0) ↔ (0 : ℝ) ∈ Set.Icc lo hi := by -- --- PROOF ---
  constructor
  · -- necessary: the zero is a value, so it lies between the least and the greatest
    rintro ⟨y, hy, hy0⟩
    exact ⟨hy0 ▸ hlo.2 ⟨y, hy, rfl⟩, hy0 ▸ hhi.2 ⟨y, hy, rfl⟩⟩
  · -- sufficient: both extrema are taken, and `g` takes every value between them on `S`
    intro h0
    obtain ⟨a, ha, rfl⟩ := hlo.1
    obtain ⟨b, hb, rfl⟩ := hhi.1
    obtain ⟨y, hy, hy0⟩ := hS.intermediate_value ha hb hg h0
    exact ⟨y, hy, hy0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
