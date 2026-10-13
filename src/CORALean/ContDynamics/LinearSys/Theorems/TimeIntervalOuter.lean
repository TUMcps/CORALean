module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepOuterSegments

@[expose] public section

/-!
# `timeIntervalStep` contains the flow at every time in the step

CORA's `HR([0,r]) = CH(X₀, e^{Ar}X₀) ⊕ F X₀`, and the guarantee that makes it
usable: not just at the sample times, but at every `t` in `[0, r]`, one named
time at a time — `timeIntervalStep_outer`, the quantified statement through
`reachExact`, is what a caller with no particular `t` in hand wants, and is
proved from this one. The wrapping-effect-free construction of [1, Alg. 1], one
step of it.

`timeIntervalStep_outer_segments` is the whole argument, at the level of `Set`s;
this is that composed with `LinComb.linComb_outer` and `Plus.plus_outer`, the two
lifts it takes to land in `construct (timeIntervalStep ...)`.

Homogeneous only: with a non-zero input a trajectory also picks up the input
integral, which is `TrajectoryTimeIntervalOuter`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- Every image of the initial set under the flow, at a named time of the step.
`timeIntervalStep_outer` is the same guarantee, quantified over every such
time at once. -/
theorem LinearSys.timeIntervalStep_outer_at (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStep r (m + 2) X₀) := by -- --- PROOF ---
  -- the two lifts `timeIntervalStep_outer_segments` stops short of
  refine (sys.timeIntervalStep_outer_segments hr hε X₀ ht0 htr).trans
    ((Set.add_subset_add ?_ subset_rfl).trans (Plus.plus_outer _ _))
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  exact LinComb.linComb_outer _ _
    ⟨y₁, hy₁, y₂, Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl hy₂), lam, hlam, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
