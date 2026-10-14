module

public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryDiscretizeStep
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnMono
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PostEvalOn
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter

@[expose] public section

/-!
# [1, Thm. 1]: a reachable subset read off the computed set

The exact reachable set of a run started inside `X₀.evalOn (Bs 0)` lies, at
every step boundary, inside the computed set evaluated at the factors that name
it — [1, (25)] with [1, Lemma 5]'s induction run on the loop itself rather than
on an abstract chain.

Nothing on the left is computed: the run is the exact flow, not `reach` of a
sub-initial set, so the reduction of [1, Alg. 1] appears on one side only and no
monotonicity of `reduce` is needed — [1]'s own route through `reach(X₀(α), …)`
would need it, and `reduce` is a function of the representation.

`Bs` is data because the factor domain grows and is renumbered as the loop runs;
`hnext` is the one condition on it, `postBox` per step, and `post_evalOn` is
what discharges the step.

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
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a run of the nonlinear system started inside the evaluated
initial set stays inside the computed set's evaluation, at every step. -/
theorem NonlinearSys.Trajectory.relinReach_evalOn {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : 𝒫𝒵 n} {U : 𝒫𝒵 m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {steps : ℕ → sys.LinStep (S := 𝒫𝒵) U} {Ud : ℕ → 𝒫𝒵 n} {Δt : ℝ} {N o : ℕ} (ho : 0 < o)
    (traj : sys.Trajectory (S := 𝒫𝒵) T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (hU : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hUd : ∀ i < N, (NonlinearSys.linearize (steps i).A).stepInput
      (fun t => sys.f (x t) (u t) - (steps i).A *ᵥ x t) Δt i ∈ construct (Ud i))
    (X₀ : 𝒫𝒵 n) (Bs : ∀ i, Set (Fin (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud).p →
      ℝ))
    (h0 : construct R₀ ⊆ X₀.evalOn (Bs 0))
    (hunit : ∀ i, ∀ a ∈ Bs i, ∀ k, |a k| ≤ 1)
    (hnext : ∀ i, PolyZonotope.postBox ((NonlinearSys.linearize (steps i).A).discretize Δt).A
      (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud) (Ud i) o (Bs i) ⊆ Bs (i + 1)) :
    ∀ i ≤ N, x ((i : ℝ) * Δt)
      ∈ (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud).evalOn
        (Bs i) := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _
    rw [show (((0 : ℕ) : ℝ) * Δt) = 0 from by norm_num]
    exact h0 traj.init
  | succ i ih =>
    intro hi
    have hiN : i < N := Nat.lt_of_succ_le hi
    have hwin : Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt) ⊆ T :=
      step_subset_horizon hΔt hT hiN
    -- step `i`'s linearized run, and the sample it takes over that window
    have hlin := (traj.restrict hwin).linearize (steps i).cert (hR i hiN)
    have hstep := hlin.discretize_step hΔt (hU i hiN) i subset_rfl
    rw [Scalar.toRealMat_real] at hstep
    have hmem : x (((i : ℝ) + 1) * Δt)
        ∈ (((NonlinearSys.linearize (steps i).A).discretize Δt).A *ᵥ ·)
            '' (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud).evalOn (Bs i)
          + construct (Ud i) := by
      rw [hstep]
      exact Set.add_mem_add ⟨_, ih hiN.le, rfl⟩ (hUd i hiN)
    -- one post step, then the sub-box the loop's own bookkeeping leaves it in
    rw [show (((i + 1 : ℕ) : ℝ) * Δt) = (((i : ℝ) + 1) * Δt) from by push_cast; ring]
    exact PolyZonotope.evalOn_mono _ (hnext i)
      (PolyZonotope.post_evalOn _ _ (Ud i) o (hunit i) hmem)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
