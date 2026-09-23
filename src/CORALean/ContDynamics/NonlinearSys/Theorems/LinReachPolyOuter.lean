import CORALean.ContDynamics.NonlinearSys.Operations.LinStepLinInput
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPoly
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolySearchEqSome
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizon

/-!
# `linReachPoly`'s step is sound

Whatever step `linReachPoly` returns, a run that stays in the region it certified over
the step's window is inside the linearized system's reachable set at the step's end,
the error it certified widening the input. `reach_outer_horizon` at `K = 1` does the
work, at the step's own certificate; what is read off the `some` is only that the
step is the linearization at the `A` the run was handed, `abstrErrPolySearch_eq_some`.

Confinement stays a hypothesis, on the certified region `step.R`, which is candidate
`k`'s `Rinit.dependent ⊞ (Rdiff + RallError)` over the whole factor box: CORA
concludes it from `trueError ≤ appliedError`, which this tree does not reproduce, and
`confinement_of_subset` discharges it from the computed sets as for any other step.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run from `Rinit` confined to the region `linReachPoly` certified is, at `Δt`,
inside the reachable set of the system linearized at `A`. -/
theorem NonlinearSys.Trajectory.linReachPoly_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {U : PolyZonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {H : Fin n → Mat ℝ (n + m) (n + m)}
    {E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m)} {Δt : ℝ}
    {η errorOrder intermediateOrder : ℕ} {Rinit Ud : PolyZonotope (Vec ℝ n)}
    {abstrerr : Vec ℝ n} {fuel : ℕ} {step : sys.LinStep (S := 𝒫𝒵) U}
    (traj : sys.Trajectory (S := 𝒫𝒵) T Rinit U x u)
    (h : sys.linReachPoly U A B xs us H E Δt η errorOrder intermediateOrder Rinit abstrerr fuel
      = some step)
    (hT : Set.Icc 0 Δt ⊆ T) (hR : ∀ t ∈ Set.Icc 0 Δt, x t ∈ step.R) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct step.linInput))
    (hUd : (NonlinearSys.linearize A).stepInput
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) Δt 0 ∈ construct Ud) {o : ℕ} (ho : 0 < o) :
    x Δt ∈ construct (((NonlinearSys.linearize A).discretize Δt).reach (S := 𝒫𝒵)
      o ho Rinit Ud 1) := by -- --- PROOF ---
  -- the step is the linearization at the `A`, `B`, `xs`, `us` the run was handed
  unfold NonlinearSys.linReachPoly at h
  obtain ⟨k, -, hA, hB, hxs, hus, -, -⟩ := NonlinearSys.abstrErrPolySearch_eq_some h
  rcases step with ⟨A', B', xs', us', R', L', cert⟩
  obtain rfl : A' = A := hA
  obtain rfl : B' = B := hB
  obtain rfl : xs' = xs := hxs
  obtain rfl : us' = us := hus
  -- one step of the linearized guarantee, at horizon `1`
  have key := traj.reach_outer_horizon (K := 1) cert (by simpa using hT) (by simpa using hR)
    hΔt hU (fun k hk => by rwa [Nat.lt_one_iff.mp hk]) ho 1 le_rfl
  simpa using key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
