module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-!
# A family of sets that eventually lies in every ball has radius tending to `0`

The measure of size used for the "`→ 0`" of [1, Prop. 3] (and Prop. 4): the radius
`sup_{v ∈ S} ‖v‖` of a
family `S x` of sets of `Vec ℝ n` (the sup norm of `Vec`) tends to `0` along a filter iff, for
every `ε > 0`, `S x ⊆ B_ε(0)` eventually. Here the direction the propositions need.

## Inputs
* `l` – filter
* `S` – family of sets

## Hypotheses
* `h` – the sets eventually lie in every ball around zero

## Conclusion
* the radius of the sets tends to zero

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Filter Topology

variable {n : ℕ} {ι : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.tendsto_sSup_norm_of_eventually_subset_closedBall {l : Filter ι}
    {S : ι → Set (Vec ℝ n)}
    (h : ∀ ε > 0, ∀ᶠ x in l, S x ⊆ Metric.closedBall (0 : Vec ℝ n) ε) :
    Tendsto (fun x => sSup ((fun v => ‖v‖) '' S x)) l (𝓝 0) := by -- --- PROOF ---
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with x hx
  have h0 : 0 ≤ sSup ((fun v => ‖v‖) '' S x) :=
    Real.sSup_nonneg (by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v)
  have h1 : sSup ((fun v => ‖v‖) '' S x) ≤ ε / 2 := by
    refine Real.sSup_le ?_ (half_pos hε).le
    rintro _ ⟨v, hv, rfl⟩
    simpa using hx hv
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
