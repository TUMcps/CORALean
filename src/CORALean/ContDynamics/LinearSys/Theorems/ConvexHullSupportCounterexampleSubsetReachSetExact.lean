module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSys.Operations.SupportCounterexample
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormHeldInput
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactConvex
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryHeldInput

@[expose] public section

/-!
# The support vectors' convex hull is an inner approximation

[1, Sec. 4.2]: for template directions `ℓ_1, …, ℓ_w`, the vertex polytope
`⟨[ν(Ř(t_k), ℓ_1), …, ν(Ř(t_k), ℓ_w)]⟩_V` lies in `R(t_k)`. Each vertex is
[1]'s Eq. (18)'s `x(k)` from `supportCounterexample`, hence the state at `t_k` of a
held-input `IsTrajectory`, and `reachSetExact_convex` takes the hull. Along its own
direction each vertex attains line 15's bound (`heldSim_supportCounterexample`).

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

/-- [1, Sec. 4.2]: the convex hull of the simulated support vectors, one per direction `ℓ j`,
lies in the exact reachable set `R(t_k)`. -/
theorem LinearSys.convexHull_supportCounterexample_subset_reachSetExact (sys : LinearSys 𝕋 n)
    (R₀ U : S n) (hR₀ : Convex ℝ (construct R₀)) (hUconv : Convex ℝ (construct U))
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt)
    {ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct R₀)
    (hνU : ∀ d, νU d ∈ construct U) {ι : Type} (ℓ : ι → Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) : -- --- STMT ---
    convexHull ℝ (Set.range fun j => sys.heldSim Δt
        (sys.supportCounterexample Δt ν₀ νU (ℓ j) k).1
        (sys.supportCounterexample Δt ν₀ νU (ℓ j) k).2 k)
      ⊆ sys.reachSetExact (Set.Icc 0 (k * Δt)) R₀ U (k * Δt) :=
  convexHull_min (Set.range_subset_iff.mpr fun _ =>
      ⟨_, _, sys.isTrajectory_heldInput R₀ U hU (mul_nonneg k.cast_nonneg hΔt.le) Δt (hν₀ _)
        (fun _ => hνU _),
        sys.closedForm_heldInput hU hΔt _ (fun _ => hνU _) k⟩)
    (sys.reachSetExact_convex (mul_nonneg k.cast_nonneg hΔt.le) hR₀ hUconv hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
