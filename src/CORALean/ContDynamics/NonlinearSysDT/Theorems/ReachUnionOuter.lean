module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubsetOn
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# A union `reachUnion` returns contains every state reached within the horizon

The run-time tests are what the proof spends: a returned union means every
test passed, `contains_sound` and `region_subset` turn each into the set
inclusion `confinement_of_subset_on` asks for, and that confinement is the
hypothesis `reach_outer_on` places the run with. No confinement is assumed of
any run; `none` is where it could not be shown.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋] [∀ n, Contains (Rg n) (S n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.WithSteps.reachUnion_outer (sys : NonlinearSysDT.WithSteps S Rg 𝕋 m n)
    (params : Reach.Params (S n) ℕ) (options : NonlinearSysDT.ReachOptions) : -- --- STMT ---
    ∀ R ∈ sys.reachUnion params options,
      sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
        ⊆ construct R := by -- --- PROOF ---
  intro R (hR : sys.reachUnion params options = some R) y hy
  simp only [NonlinearSysDT.WithSteps.reachUnion] at hR
  split at hR
  case isFalse => exact absurd hR (by simp)
  case isTrue hconf =>
    -- every test passed, so each step `k < K` starts inside its certified region
    have hsub : ∀ k < params.tFinal - params.tStart,
        construct (sys.sys.reach ⟨params.X₀, sys.U, 0, k⟩ options sys.steps)
          ⊆ (sys.steps k).R :=
      fun k hk => (Contains.contains_sound _ _
        (List.all_eq_true.mp hconf k (List.mem_range.mpr hk))).trans (sys.region_subset k)
    obtain ⟨k, hk, x, u, traj, rfl⟩ := Set.mem_iUnion₂.mp hy
    -- the run from the bare set `construct R0` is a run from the representation `R0`
    have traj' : sys.sys.IsTrajectoryOn params.X₀ sys.U (params.tFinal - params.tStart) x u
        (fun k => sys.sys.g (x k) (u k)) :=
      ⟨traj.init, traj.input, traj.step, traj.output⟩
    have hx := sys.sys.reach_outer_on options.hZonotopeOrder sys.steps params.X₀ traj'
      (sys.sys.confinement_of_subset_on options.hZonotopeOrder sys.steps params.X₀ hsub traj')
      k hk
    rw [← Option.some_inj.mp hR]
    exact SetUnion.mem_construct_range (Nat.lt_succ_of_le hk) hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
