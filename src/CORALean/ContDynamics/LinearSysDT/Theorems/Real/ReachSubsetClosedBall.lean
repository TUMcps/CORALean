module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe

@[expose] public section

/-!
# The reachable set's sup-norm ball over a whole run, at a fixed order

`aux_reach_step_subset_closedBall` leaves its box term a hypothesis; here it is discharged by
`aux_reduceBox_absBound_le`, which needs nothing about the order — the box a step pays is never
wider than that step's own pre-reduction zonotope. That crudeness is the whole cost: the true
reduction can throw away far less once the order is past a handful of generators, and
`reach_subset_closedBall_of_reduceBoxOrder` is where a caller-stated tolerance buys that back. What
results is `(2 * ‖sys.A‖) ^ k * r₀ + 2 * rU * ∑ⱼ<ₖ (2 * ‖sys.A‖) ʲ`, [1]'s shape, with a `2` folded
into the base because domination pays the box term at the pre-reduction radius twice. No sharper
form is proved: `Do not state a sharper closed form than you prove`.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `r₀` – radius of the initial set
* `rU` – radius of the input set
* `k` – step

## Hypotheses
* `ho` – order positive
* `hR₀` – initial set lies in its ball
* `hr₀` – initial radius nonnegative
* `hU` – input set lies in its ball
* `hrU` – input radius nonnegative

## Conclusion
* the reachable set lies in a ball with a geometric radius

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
/-- The box's own `absBound`, read off its diagonal generators at a
coordinate: the dropped rows' `1`-norm there, and nothing from the center. -/
private theorem aux_reduceByBox_absBound {n q r : ℕ} (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (j : Fin n) : -- --- CONCL ---
    (Z.reduceByBox part).absBound j = ∑ l, |Z.G (part.right l) j| := by -- --- PROOF ---
  show |(0 : Vec ℝ n) j| + ∑ l : Fin n,
      |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) l j| = ∑ l, |Z.G (part.right l) j|
  rw [Pi.zero_apply, abs_zero, zero_add]
  have hsingle : (∑ l, |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) l j|)
      = |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) j j| :=
    Finset.sum_eq_single j (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb, abs_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
  rw [hsingle, Matrix.diagonal_apply_eq,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]


/-- `reduceBox`'s own `absBound` never exceeds the source zonotope's: a
dropped generator is one of `Z`'s own, and the origin at an order already met
is no further than `Z`'s own center, `absBound` being non-negative. -/
private theorem Zonotope.aux_reduceBox_absBound_le (Z : Zonotope (Vec ℝ n)) (o : ℕ)
    (j : Fin n) : -- --- CONCL ---
    (Z.reduceBox o).absBound j ≤ Z.absBound j := by -- --- PROOF ---
  unfold Zonotope.reduceBox
  split_ifs with hlt
  · rw [aux_reduceByBox_absBound]
    calc ∑ l, |Z.G ((Z.girardSplit o hlt).right l) j|
        ≤ ∑ l, |Z.G ((Z.girardSplit o hlt).left l) j|
            + ∑ l, |Z.G ((Z.girardSplit o hlt).right l) j| :=
          le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = ∑ l, |Z.G l j| := ((Z.girardSplit o hlt).sum_split₂ fun l => |Z.G l j|).symm
      _ ≤ Z.absBound j := by
          rw [Zonotope.absBound]; exact le_add_of_nonneg_left (abs_nonneg _)
  · rw [Zonotope.absBound]
    simp only [Zonotope.ofPoint, Pi.zero_apply, abs_zero, zero_add, Finset.univ_eq_empty,
      Finset.sum_empty]
    rw [Zonotope.absBound]; positivity
end Real


section
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Step `k + 1` of `reach` reaches no further than `‖sys.A‖ * r + rU + rbox`,
given a ball for the state reached at step `k`, one for `U`, and one for the
box that step's own reduction pays. -/
private theorem LinearSysDT.aux_reach_step_subset_closedBall (sys : LinearSysDT ℝ n) {o : ℕ}
    (ho : 0 < o) {R₀ U : Zonotope (Vec ℝ n)} {r rU rbox : ℝ} (k : ℕ)
    (hR : (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU)
    (hbox : (((Zonotope.mtimes sys.A
        (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U).reduceBox o).construct
        ⊆ Metric.closedBall (0 : Vec ℝ n) rbox) :
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * r + rU + rbox) :=
  Zonotope.step_subset_closedBall sys.A hR hU hbox

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach`'s state at step `k` reaches no further than a geometric run in
`2 * ‖sys.A‖` applied to the initial ball, plus the same sum applied to the
input's — crude, from bounding a step's box by its own pre-reduction width. -/
theorem LinearSysDT.reach_subset_closedBall (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec ℝ n)} {r₀ rU : ℝ}
    (hR₀ : R₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r₀) (hr₀ : 0 ≤ r₀)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU) (hrU : 0 ≤ rU)
    (k : ℕ) : -- --- CONCL ---
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
        (Zonotope.aux_reduceBox_absBound_le _ o j).trans
          (Zonotope.absBound_le_of_subset_closedBall hpre j)
    have hstep := LinearSysDT.aux_reach_step_subset_closedBall sys ho k ih hU hbox
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
