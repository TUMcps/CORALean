import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct
import CORALean.ContSet.ContSet.Definitions.ConvexSet

/-!
# `timePointStep` contains every state the step can end at

The two halves of the step, each already proved: `mtimes` carries the initial
set by `e^{Ar}` and `inputReach_subset_inputSolution` is [1, Thm. 3.1] for
what the input adds, with its six topological hypotheses read off the
representation as `ReachOuterConvexCompact` does.

`0 ∈ U` is not needed. The step ends at `r`, so no earlier time has to be
covered, which is what asks for the zero input elsewhere — [1, Prop. 3.3] is
where that hypothesis belongs.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ U : S n) :
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
