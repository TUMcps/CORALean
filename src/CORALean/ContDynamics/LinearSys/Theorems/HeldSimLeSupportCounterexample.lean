module

public import CORALean.ContDynamics.LinearSys.Operations.SupportCounterexample
public import CORALean.ContDynamics.LinearSys.Theorems.HeldSimEq

@[expose] public section

/-!
# The corrected counterexample is a support vector of the held-input reach set

[1, Sec. 4.2] calls the simulated `x(k)` the support vector `ν(Ř(t_k), ℓ)`: no
initial state of `X₀` and no input sequence in `U`, held over the steps, reaches
further along `ℓ` at `t_k`. With `supportCounterexample`'s inputs, which maximize
`(e^{A t_{k-1-j}} T)ᵀ ℓ` over `U` at step `j`, this holds term by term in
`heldSim_eq`; with the printed Eq. (20) it does not
(`printedSupportInput_counterexample`).

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2], with Eq. (20) corrected: if `ν₀` and `νU` are support vectors of `X₀` and `U`,
every held-input state at `t_k` from `X₀` under inputs in `U` is at most
`supportCounterexample`'s along `ℓ`. -/
theorem LinearSys.heldSim_le_supportCounterexample (sys : LinearSys 𝕋 n) (Δt : ℝ)
    {X₀ U : Set (Vec ℝ n)} {ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n}
    (hν₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, ∀ x ∈ X₀, d x ≤ d (ν₀ d))
    (hνU : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, ∀ y ∈ U, d y ≤ d (νU d)) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ X₀) {u : ℕ → Vec ℝ n} (hu : ∀ j, u j ∈ U) :
    ℓ (sys.heldSim Δt x₀ u k)
      ≤ ℓ (sys.heldSim Δt (sys.supportCounterexample Δt ν₀ νU ℓ k).1
          (sys.supportCounterexample Δt ν₀ νU ℓ k).2 k) := by -- --- PROOF ---
  rw [sys.heldSim_eq, sys.heldSim_eq, map_add, map_add, map_sum, map_sum]
  exact add_le_add (hν₀ (ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ k))) x₀ hx₀)
    (Finset.sum_le_sum fun i _ => hνU
      ((ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ (k - 1 - i)))).comp
        (mulVecLin (MatExp.expIntegral (toRealMat sys.A) Δt))) (u i) (hu i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
