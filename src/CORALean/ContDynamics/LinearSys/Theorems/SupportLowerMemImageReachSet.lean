import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormHeldInput
import CORALean.ContDynamics.LinearSys.Theorems.HeldSimSupportCounterexample
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryHeldInput

/-!
# Line 15's lower bound is a value the reachable set takes

[1, Alg. 1 (lower bounds)], line 15: `ρ(Ř(t_k), ℓ)` is `ℓ` at a state some run of
the system is in at `t_k` — the run from `supportCounterexample`'s initial state
under its held inputs, which `trajectory_heldInput` makes a `Trajectory`,
`closedForm_heldInput` samples as [1]'s Eq. (18), and
`heldSim_supportCounterexample` evaluates along `ℓ`. So it is at most
`ρ(R(t_k), ℓ)`, and `Ř(t_k)` is reached rather than enclosed.

The support vectors only have to be points of `X₀` and `U`; that they maximize is
what makes the bound tight, not what makes it a bound.

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

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (lower bounds)]: line 15's `ρ(Ř(t_k), ℓ)` is `ℓ` at a point of the exact
reachable set `R(t_k)`. -/
theorem LinearSys.supportLower_mem_image_reachSet (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt)
    {ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct R₀)
    (hνU : ∀ d, νU d ∈ construct U) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportLower Δt ν₀ νU c ℓ k).ρR
      ∈ ℓ '' sys.reachSet (Set.Icc 0 (k * Δt)) R₀ U (k * Δt) := by -- --- PROOF ---
  set cex := sys.supportCounterexample Δt ν₀ νU ℓ k
  have hv : ∀ j, cex.2 j ∈ construct U := fun _ => hνU _
  refine ⟨sys.closedForm cex.1 (LinearSys.heldInput Δt cex.2) (k * Δt),
    ⟨_, _, sys.trajectory_heldInput R₀ U hU (mul_nonneg k.cast_nonneg hΔt.le) Δt (hν₀ _) hv,
      rfl⟩, ?_⟩
  rw [sys.closedForm_heldInput hU hΔt cex.1 hv k]
  exact sys.heldSim_supportCounterexample Δt ν₀ νU c ℓ k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
