module

public import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionSubsetConstInputAddErrorBox
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# The sampled exact recursion, against held inputs

`LinearSysDT.reachSet` of the sampled system under `inputSolution`, the input
set a run adds at every step, stays inside the same recursion under the input
set of one held input per step, widened by `reachInputError`.

By induction on the step count, and linear on both sides: the state part and the
error part each pass through `e^{AΔt}` separately, and the step's own input
splits by `inputSolution_subset_constInput_add_errorBox` into a held-input point
and a point of that step's error box.

The recursion on the right is the zero-order-hold reachable set, which
`discretize_reachSet_subset_inputReach` places inside `inputReach`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sampled recursion under `inputSolution` stays inside the recursion under
held inputs, widened by the input enclosures' accumulated error. -/
theorem LinearSys.discretize_reachSet_subset_add_reachInputError (sys : LinearSys 𝕋 n)
    {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.discretize Δt).reachSet (S := 𝒵) R₀ (sys.inputSolution (S := 𝒵) Δt η U) k
      ⊆ (sys.discretize Δt).reachSet (S := 𝒵) R₀
          (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U) k
        + (sys.reachInputError Δt η U k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    -- nothing is owed yet, and every point of `R₀` is itself plus the origin
    intro x hx
    have h := Set.add_mem_add hx (Zonotope.mem_ofPoint (0 : Vec ℝ n))
    rwa [add_zero] at h
  | succ k ih =>
    rintro _ ⟨_, ⟨y, hy, rfl⟩, d, hd, rfl⟩
    obtain ⟨a, ha, e, he, rfl⟩ := ih hy
    obtain ⟨q, hq, b, hb, rfl⟩ := sys.inputSolution_subset_constInput_add_errorBox hΔt η hε U hd
    -- the held-input part and the error part, each carried through this step's `e^{AΔt}`
    refine ⟨toRealMat (sys.discretize Δt).A *ᵥ a + q, ⟨_, ⟨a, ha, rfl⟩, q, hq, rfl⟩,
      (sys.discretize Δt).A *ᵥ e + b, ?_, ?_⟩
    · show _ ∈ ((Zonotope.mtimes (sys.discretize Δt).A (sys.reachInputError Δt η U k)).plus
        (sys.timePointStepErrorBox Δt η U)).construct
      rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
      exact Set.add_mem_add ⟨e, he, rfl⟩ hb
    · show toRealMat (sys.discretize Δt).A *ᵥ a + q + ((sys.discretize Δt).A *ᵥ e + b)
        = toRealMat (sys.discretize Δt).A *ᵥ (a + e) + (q + b)
      rw [Scalar.toRealMat_real, Matrix.mulVec_add]
      abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
