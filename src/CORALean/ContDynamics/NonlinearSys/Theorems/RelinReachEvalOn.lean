module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.Theorems.StepInputShift
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeWindow
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnMono
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PostEvalOn
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter

@[expose] public section

/-!
# [1, Thm. 1]: a reachable subset read off the computed set

The exact reachable set of a run started inside `X₀.evalOn (Bs 0)` lies, at every step boundary,
inside the computed set evaluated at the factors that name it: [1, (25)] with [1, Lemma 5]'s
induction run on the loop itself. Nothing on the left is computed: the run is the exact flow, not
`reach` of a sub-initial set, so the reduction of [1, Alg. 1] appears on one side only and no
monotonicity of `reduce` is needed. `Bs` is data because the factor domain grows and is
renumbered as the loop runs; `hnext` is the one condition on it, `postBox` per step, and
`post_evalOn` discharges the step.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `steps` – linearization steps
* `Ud` – input enclosures per step
* `Δt` – step size
* `N` – number of steps
* `o` – maximum order
* `y` – output trajectory
* `X₀` – sub-initial set
* `Bs` – factor domains

## Hypotheses
* `ho` – order positive
* `traj` – trajectory of the system
* `hΔt` – step size nonnegative
* `hT` – horizon inside time set
* `hR` – trajectory stays in regions
* `hU` – widened inputs bounded
* `hUd` – input enclosures hold step inputs
* `h0` – initial set inside evaluated set
* `hunit` – factor domains bounded by one
* `hnext` – factor domains closed under steps

## Conclusion
* the trajectory state lies in the computed set evaluated at the subset factors

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   18-October-2026
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
theorem NonlinearSys.IsTrajectory.relinReach_evalOn {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : 𝒫𝒵 n} {U : 𝒫𝒵 m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {steps : ℕ → sys.LinStep (S := 𝒫𝒵) U} {Ud : ℕ → 𝒫𝒵 n} {Δt : ℝ} {N o : ℕ} (ho : 0 < o)
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒫𝒵) T R₀ U x u y) (hΔt : 0 ≤ Δt)
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
      (sys.relinReach (S := 𝒫𝒵) ⟨X₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud) (Ud i) o (Bs i) ⊆ Bs (i + 1))
    : -- --- CONCL ---
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
    have hexp : ((i : ℝ) + 1) * Δt = (i : ℝ) * Δt + Δt := by ring
    rw [hexp] at hwin
    have hlin := traj.linearize_window (A := (steps i).A) (V := construct (steps i).linInput) hΔt
      hwin fun t ht => linInput_outer (steps i).cert (hR i hiN t (hexp ▸ ht))
        (traj.input t (hwin ht))
    have hstep := hlin.discretize_step hΔt (hU i hiN) 0 (by simp)
    have hshift := (NonlinearSys.linearize (steps i).A).stepInput_shift
      (fun s => sys.f (x s) (u s) - (steps i).A *ᵥ x s) Δt i
    rw [Scalar.toRealMat_real, hshift] at hstep
    simp only [Nat.cast_zero, zero_add, one_mul, zero_mul, add_zero] at hstep
    rw [← hexp] at hstep
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
