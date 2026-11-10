module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachExactAt
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSetLinComb

@[expose] public section

/-!
# `timeInterval` contains the flow at every time in the step

CORA's `HR([0,r]) = CH(X₀, e^{Ar}X₀) ⊕ F X₀`, and the guarantee that makes it usable: not just at
the sample times, but at every `t` in `[0, r]`, one named time at a time. `timeInterval_outer`, the
quantified statement through `reachExact`, is what a caller with no particular `t` in hand wants,
and is proved from this one. The first window of [1, Sec. V-B], at a single matrix, which every
later window is an image of. `timeInterval_outer_setLinComb` is the whole argument, at the level of
`Set`s; this is that composed with `LinComb.linComb_outer` and `Plus.plus_outer`. Homogeneous only:
with a non-zero input a trajectory also picks up the input integral, which is
`TrajectoryTimeIntervalOuter`.

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet n) (Vec ℝ n)] [∀ n, LinComb (ContSet n) (Vec ℝ n)]
variable [∀ n, Reduce (ContSet n) (Vec ℝ n)] [Mtimes (Mat ℝ) ContSet]
variable [Mtimes ℐ ContSet]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (ContSet n) (Vec ℝ n)] [Mtimes (Mat ℝ) ContSet] in
/-- Every image of the initial set under the flow, at a named time of the step.
`timeInterval_outer` is the same guarantee, quantified over every such
time at once. -/
theorem LinearSys.timeInterval_outer_at (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ X₁ : ContSet n)
    (hX : sys.reachExactAt r (toSet X₀) ⊆ toSet X₁)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' toSet X₀
      ⊆ toSet (sys.timeInterval r (m + 2) X₀ X₁) := by -- --- PROOF ---
  -- the two lifts `timeInterval_outer_setLinComb` stops short of
  refine (sys.timeInterval_outer_setLinComb hr hε X₀ ht0 htr).trans
    ((Set.add_subset_add ?_ subset_rfl).trans (Plus.plus_outer _ _))
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  exact LinComb.linComb_outer _ _
    ⟨y₁, hy₁, y₂, hX hy₂, lam, hlam, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
