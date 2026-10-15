module

public import CORALean.ContDynamics.LinearSys.Theorems.IsClassicalTrajectoryStepInputOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachEvalOn

@[expose] public section

/-!
# [1, Thm. 1] on the reachable set, with each step's input enclosure named

`relinReach_evalOn` restated on `reachSet`: what it says of every run at `iΔt`,
this says of the exact reachable set of the sub-initial set at once, which is
what [1, (25)] claims — `Rᵉ` on the left, the computed polynomial zonotope
evaluated at the parameters naming the subset on the right.

`Ud` is named rather than assumed, as in `relinReach_outer_inputSolution`, so
the only hypotheses left about a step are `stepInput_outer`'s: the truncation
bound and the properties of that step's `linInput`. The confinement is asked of
`reachSet`, which `reachSet_confinement_of_subset` discharges from a check on
the computed sets.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Mtimes

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the exact reachable set of the sub-parameterized initial set
lies inside the computed set evaluated at the factors naming that subset. -/
theorem NonlinearSys.reachSet_subset_evalOn (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : 𝒫𝒵 n) (U : 𝒫𝒵 m) {steps : ℕ → sys.LinStep (S := 𝒫𝒵) U}
    {Δt : ℝ} {N : ℕ} (hΔt : 0 < Δt) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      sys.reachSet (S := 𝒫𝒵) T R₀ U t ⊆ (steps i).R)
    -- the nine `stepInput_outer` hypotheses, each about step `i`'s own linearization
    (η : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / ((η : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hRconv : ∀ i < N, Convex ℝ (construct (mtimes (𝕄 := ℐ) (S := 𝒫𝒵)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (mtimes (𝕄 := ℐ) (S := 𝒫𝒵)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (mtimes (𝕄 := ℐ) (S := 𝒫𝒵)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (Ud : ℕ → 𝒫𝒵 n)
    (hUd : ∀ i < N, construct ((NonlinearSys.linearize (steps i).A).inputSolution
      (S := 𝒫𝒵) Δt η (steps i).linInput) ⊆ construct (Ud i))
    -- and the evaluation, carried by the sub-boxes the loop's own bookkeeping leaves
    {o : ℕ} (ho : 0 < o) (X₀ : 𝒫𝒵 n)
    (Bs : ∀ i, Set (Fin (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud).p → ℝ))
    (h0 : construct R₀ ⊆ X₀.evalOn (Bs 0))
    (hunit : ∀ i, ∀ a ∈ Bs i, ∀ k, |a k| ≤ 1)
    (hnext : ∀ i, PolyZonotope.postBox ((NonlinearSys.linearize (steps i).A).discretize Δt).A
      (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud) (Ud i) o (Bs i) ⊆ Bs (i + 1)) :
    ∀ i ≤ N, sys.reachSet (S := 𝒫𝒵) T R₀ U ((i : ℝ) * Δt)
      ⊆ (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud).evalOn
        (Bs i) := by -- --- PROOF ---
  rintro i hi _ ⟨x, u, traj, rfl⟩
  -- every step's input integral enclosed on the original clock, as [1, Alg. 1] leaves it
  have hstep : ∀ j < N, (NonlinearSys.linearize (steps j).A).stepInput
      (fun t => sys.f (x t) (u t) - (steps j).A *ᵥ x t) Δt j ∈ construct (Ud j) := by
    intro j hj
    have hlin := (traj.restrict (step_subset_horizon hΔt.le hT hj)).linearize (steps j).cert
      (fun t ht => hR j hj t ht (traj.reachSet_outer t))
    exact hUd j hj (hlin.stepInput_outer hΔt η (hε j hj) (hconv j hj) (hclosed j hj)
      (hbdd j hj) (hRconv j hj) (hRclosed j hj) (hRbdd j hj) j subset_rfl)
  exact traj.relinReach_evalOn ho hΔt.le hT
    (fun j hj t ht => hR j hj t ht (traj.reachSet_outer t)) hbdd hstep X₀ Bs h0 hunit hnext i hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
