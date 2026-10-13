module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachStepSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxAbsBoundLe
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe

@[expose] public section

/-!
# The reachable set's sup-norm ball over a whole run, at a fixed order

`reach_step_subset_closedBall` leaves its box term a hypothesis; here it is
discharged by `reduceBox_absBound_le`, which needs nothing about the order —
the box a step pays is never wider than that step's own pre-reduction
zonotope, so a run bounded so far bounds its own next box for free. That
crudeness is the whole cost: the true reduction can throw away far less than
its own width once the order is past a handful of generators, and
`reach_subset_closedBall_of_reduceBoxOrder` is where a caller-stated tolerance
buys that back.

What results is `(2 * ‖sys.A‖) ^ k * r₀ + 2 * rU * ∑ⱼ<ₖ (2 * ‖sys.A‖) ʲ`, [1]'s
shape — a geometric run in the matrix norm applied to the initial ball, plus a
geometric sum of it against the input's — with a `2` folded into the base
because domination pays the box term at the pre-reduction radius twice, not
once. No sharper form is proved: `Do not state a sharper closed form than you
prove`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach`'s state at step `k` reaches no further than a geometric run in
`2 * ‖sys.A‖` applied to the initial ball, plus the same sum applied to the
input's — crude, from bounding a step's box by its own pre-reduction width. -/
theorem LinearSysDT.reach_subset_closedBall (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec ℝ n)} {r₀ rU : ℝ}
    (hR₀ : R₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r₀) (hr₀ : 0 ≤ r₀)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU) (hrU : 0 ≤ rU) (k : ℕ) :
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) ((2 * ‖sys.A‖) ^ k * r₀
        + 2 * rU * ∑ j ∈ Finset.range k, (2 * ‖sys.A‖) ^ j) := by -- --- PROOF ---
  induction k with
  | zero =>
    show R₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) ((2 * ‖sys.A‖) ^ 0 * r₀
      + 2 * rU * ∑ j ∈ Finset.range 0, (2 * ‖sys.A‖) ^ j)
    simpa using hR₀
  | succ k ih =>
    -- `rk` is step `k`'s radius, `W` the pre-reduction zonotope step `k + 1` reduces
    set S : ℝ := ∑ j ∈ Finset.range k, (2 * ‖sys.A‖) ^ j with hS
    set rk : ℝ := (2 * ‖sys.A‖) ^ k * r₀ + 2 * rU * S with hrk
    have hAnn : (0:ℝ) ≤ ‖sys.A‖ := norm_nonneg _
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => pow_nonneg (by positivity) j
    have hrknn : 0 ≤ rk := by
      have h1 : (0:ℝ) ≤ (2 * ‖sys.A‖) ^ k * r₀ := mul_nonneg (by positivity) hr₀
      have h2 : (0:ℝ) ≤ 2 * rU * S := mul_nonneg (by positivity) hSnn
      rw [hrk]; linarith
    have hW : (0:ℝ) ≤ ‖sys.A‖ * rk + rU := by
      have := mul_nonneg hAnn hrknn
      linarith
    set W : Zonotope (Vec ℝ n) :=
      Zonotope.plus (Zonotope.mtimes sys.A (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U with hWdef
    have hpre : W.construct ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * rk + rU) :=
      Zonotope.plus_subset_closedBall (Zonotope.mtimes_subset_closedBall sys.A ih) hU
    -- the box the reduction pays is dominated by `W`'s own reach, hence the same radius
    have hbox : (W.reduceBox o).construct
        ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * rk + rU) :=
      Zonotope.subset_closedBall_of_absBound_le hW fun j =>
        (Zonotope.reduceBox_absBound_le _ o j).trans
          (Zonotope.absBound_le_of_subset_closedBall hpre j)
    have hstep := LinearSysDT.reach_step_subset_closedBall sys ho k ih hU hbox
    -- shift the geometric sum by one term to land on step `k + 1`'s closed form
    have hgeom : (2 * ‖sys.A‖) * S + 1
        = ∑ j ∈ Finset.range (k + 1), (2 * ‖sys.A‖) ^ j := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
      rw [pow_succ']
    have hradius : ‖sys.A‖ * rk + rU + (‖sys.A‖ * rk + rU)
        = (2 * ‖sys.A‖) ^ (k + 1) * r₀
          + 2 * rU * ∑ j ∈ Finset.range (k + 1), (2 * ‖sys.A‖) ^ j := by
      rw [← hgeom, hrk, pow_succ]
      ring
    rwa [hradius] at hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
