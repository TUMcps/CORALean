import CORALean.ContDynamics.LinearSys.Operations.ReachError
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetSubsetAddReachInputError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSubsetReachSetAddError

/-!
# A sampled run, against held inputs and its own error

`LinearSysDT.reach_subset_reachSet_add_error` at the sampled system, composed
with `discretize_reachSet_subset_add_reachInputError`: the first takes the
reductions off the run, the second the input enclosures' excess off the exact
recursion that is left, and `reachError` is the two errors summed.

The set on the right is the zero-order-hold reachable set: `R₀` carried by
`e^{AΔt}` and one held input's contribution `(∫₀^{Δt} e^{As} ds) U` added per
step. It is a `LinearSysDT.reachSet` of zonotopes, hence convex and compact,
which is what the inner approximation needs of it.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What a sampled run computes stays inside the zero-order-hold reachable set,
widened by the error that run accumulated. -/
theorem LinearSys.reach_subset_discretize_reachSet_add_error (sys : LinearSys 𝕋 n)
    {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    ((sys.discretize Δt).reach (S := 𝒵) o ho R₀ (sys.inputSolution (S := 𝒵) Δt η U) k).construct
      ⊆ (sys.discretize Δt).reachSet (S := 𝒵) R₀
          (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U) k
        + (sys.reachError Δt η o ho R₀ U k).construct := by -- --- PROOF ---
  intro x hx
  -- the reductions come off first, then the input enclosures' excess
  obtain ⟨y, hy, e₁, he₁, rfl⟩ :=
    (sys.discretize Δt).reach_subset_reachSet_add_error ho R₀ _ k hx
  obtain ⟨a, ha, e₂, he₂, rfl⟩ :=
    sys.discretize_reachSet_subset_add_reachInputError hΔt η hε R₀ U k hy
  refine ⟨a, ha, e₁ + e₂, ?_, by dsimp only; abel⟩
  rw [LinearSys.reachError, ← Zonotope.plus_exact]
  exact Set.add_mem_add he₁ he₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
