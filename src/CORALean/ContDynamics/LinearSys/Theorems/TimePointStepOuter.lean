module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `timePointStep` contains every state the step can end at

The two halves of the step, each already proved: `mtimes` carries the initial
set by `e^{Ar}` and `inputReach_subset_inputSolution` is [1, Prop. 2] for
what the input adds, with its six topological hypotheses read off the
representation as `ReachOuterConvexCompact` does.

`0 ∈ U` is not needed. The step ends at `r`, so no earlier time has to be
covered, which is what asks for the zero input elsewhere — [2, Prop. 4] is
where that hypothesis belongs.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial set
* `U` – input set

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* every state the step can end at lies in the step set

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything the flow reaches at the end of a step, from `X₀` and under an
input in `U`, is in `timePointStep`. -/
theorem LinearSys.timePointStep_outer [∀ n, ConvexSet (S n) (Vec ℝ n)]
    [∀ n, CompactSet (S n) (Vec ℝ n)] (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ U : S n) : -- --- CONCL ---
    (fun x₀ => exp (r • toRealMat sys.A) *ᵥ x₀) '' construct X₀ + sys.inputReach U r
      ⊆ construct (sys.timePointStep r η X₀ U) := by -- --- PROOF ---
  rintro _ ⟨_, ⟨x₀, hx₀, rfl⟩, z, hz, rfl⟩
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx₀))
  · exact sys.inputReach_subset_inputSolution hr η hε (ConvexSet.convex_construct U)
      (CompactSet.isClosed_construct U) (CompactSet.isBounded_construct U)
      (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
      (CompactSet.isBounded_construct _) hz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
