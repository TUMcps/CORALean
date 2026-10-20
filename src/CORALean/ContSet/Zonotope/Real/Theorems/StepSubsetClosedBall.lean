module

public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox

@[expose] public section

/-!
# One step of `mtimes`, `plus`, `reduce` bounds the sup-norm ball it lands in

`LinearSysDT.reach`'s step is this composition: a matrix product, a Minkowski sum with the input
set, and a reduction. `mtimes_subset_closedBall` and `plus_subset_closedBall` carry a ball through
the first two; the third adds at most `reduceBox`'s own ball, `reduce_subset_add_box` supplying the
set inclusion and the triangle inequality the radius. The box's radius is a hypothesis here, since
what it can be made is the whole content of the two ways this bound gets used: a fixed order
against the source zonotope's own reach (crude, but self-contained — see
`LinearSysDT.reach_subset_closedBall`), or an order `reduceBoxOrder` chooses against a caller's
tolerance (`step_subset_closedBall_of_reduceBoxOrder`).

## Inputs
* `A` – state matrix
* `Z` – zonotope
* `U` – input zonotope
* `o` – target order
* `r` – radius of `Z`
* `rU` – radius of `U`
* `rbox` – radius of the reduction box

## Hypotheses
* `hZ` – `Z` lies in its ball
* `hU` – `U` lies in its ball
* `hbox` – the box lies in its ball

## Conclusion
* one step lies in the ball of the summed radii
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step `reduce (plus (mtimes A Z) U) o` reaches no further than
`‖A‖ * r + rU + rbox`, given a ball for each of `Z`, `U` and the box the
reduction pays at that step. -/
theorem Zonotope.step_subset_closedBall (A : Mat ℝ n n) {Z U : Zonotope (Vec ℝ n)} {o : ℕ}
    {r rU rbox : ℝ} (hZ : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU)
    (hbox : (((Zonotope.mtimes A Z).plus U).reduceBox o).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) rbox) : -- --- CONCL ---
    (((Zonotope.mtimes A Z).plus U).reduce o).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖A‖ * r + rU + rbox) := by -- --- PROOF ---
  have hW : ((Zonotope.mtimes A Z).plus U).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖A‖ * r + rU) :=
    Zonotope.plus_subset_closedBall (Zonotope.mtimes_subset_closedBall A hZ) hU
  intro x hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
    Zonotope.reduce_subset_add_box ((Zonotope.mtimes A Z).plus U) o hx
  have h1 := hW hx₁
  have h2 := hbox hx₂
  rw [Metric.mem_closedBall, dist_zero_right] at h1 h2 ⊢
  calc ‖x₁ + x₂‖ ≤ ‖x₁‖ + ‖x₂‖ := norm_add_le _ _
    _ ≤ (‖A‖ * r + rU) + rbox := add_le_add h1 h2
    _ = ‖A‖ * r + rU + rbox := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
