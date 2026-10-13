import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormHeldInput
import CORALean.ContDynamics.LinearSys.Theorems.HeldSimSupportCounterexample
import CORALean.ContDynamics.LinearSys.Theorems.SupportLowerTimeIntervalLe
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryHeldInput

/-!
# A crossed lower bound hands back a run that crosses

[1, Alg. 2], lines 9-10, with the counterexample of [1]'s Sec. 5.1: once line 16's
`ρ(Ř(τ_k), ℓ_i)` exceeds `f_(i)`, the run from `supportCounterexample` — the
initial state of [1]'s Eq. (19) and the piecewise-constant inputs of
[1]'s Eq. (20), corrected — is a `Trajectory` of the system whose state leaves the
halfspace `ℓ_i x ≤ f_(i)` at `t_k` or at `t_{k+1}`.

Which of the two is decided by line 16's maximum (`supportLower_timeInterval_le`),
and needs `ũ ∈ U` for the second; [1]'s Sec. 5.1 names only `ν(Ř(t_k), ℓ_i)`, which
is the violating one only when the maximum is `ρ(H(t_k), ℓ_i)`. The run is on
`[0, t_{k+1}]`, the whole of `τ_k`.

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

/-- [1, Alg. 2, l. 9-10]: if line 16's `ρ(Ř(τ_k), ℓ)` exceeds `f`, the run from
`supportCounterexample` at `j = k` or `j = k + 1` is a `Trajectory` on `[0, t_{k+1}]` whose
state at `t_j` has `ℓ x > f`. -/
theorem LinearSys.supportCounterexample_violates (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt)
    {ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct R₀)
    (hνU : ∀ d, νU d ∈ construct U) {c : Vec ℝ n}
    (hc : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d c ≤ d (νU d)) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) {f : ℝ} {k : ℕ}
    (hf : f < (sys.supportLower Δt ν₀ νU c ℓ (k + 1)).ρRτ) :
    ∃ j, (j = k ∨ j = k + 1) ∧
      sys.Trajectory (Set.Icc 0 ((k + 1 : ℕ) * Δt)) R₀ U
        (sys.closedForm (sys.supportCounterexample Δt ν₀ νU ℓ j).1
          (LinearSys.heldInput Δt (sys.supportCounterexample Δt ν₀ νU ℓ j).2))
        (LinearSys.heldInput Δt (sys.supportCounterexample Δt ν₀ νU ℓ j).2) ∧
      f < ℓ (sys.closedForm (sys.supportCounterexample Δt ν₀ νU ℓ j).1
        (LinearSys.heldInput Δt (sys.supportCounterexample Δt ν₀ νU ℓ j).2)
        (j * Δt)) := by -- --- PROOF ---
  have hv : ∀ j i, (sys.supportCounterexample Δt ν₀ νU ℓ j).2 i ∈ construct U :=
    fun _ _ => hνU _
  have hreach : ∀ j, ℓ (sys.closedForm (sys.supportCounterexample Δt ν₀ νU ℓ j).1
      (LinearSys.heldInput Δt (sys.supportCounterexample Δt ν₀ νU ℓ j).2) (j * Δt))
      = (sys.supportLower Δt ν₀ νU c ℓ j).ρR := fun j => by
    rw [sys.closedForm_heldInput hU hΔt _ (hv j) j]
    exact sys.heldSim_supportCounterexample Δt ν₀ νU c ℓ j
  have hx₀ : ∀ j, (sys.supportCounterexample Δt ν₀ νU ℓ j).1 ∈ construct R₀ := fun _ => hν₀ _
  have htraj := fun j => sys.trajectory_heldInput R₀ U hU
    (mul_nonneg (k + 1 : ℕ).cast_nonneg hΔt.le) Δt (hx₀ j) (hv j)
  have hle := sys.supportLower_timeInterval_le Δt ν₀ νU hc ℓ k
  rcases lt_max_iff.mp (lt_of_lt_of_le hf hle) with h | h
  · exact ⟨k, Or.inl rfl, htraj k, (hreach k).symm ▸ h⟩
  · exact ⟨k + 1, Or.inr rfl, htraj (k + 1), (hreach (k + 1)).symm ▸ h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
