import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachUnion
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubsetOn

/-!
# A union `reachUnion` returns contains every state reached within the horizon

The run-time tests are what the proof spends: a returned union means every
test passed, `contains_sound` and `region_subset` turn each into the set
inclusion `confinement_of_subset_on` asks for, and that confinement is the
hypothesis `reach_outer_on` places the run with. No confinement is assumed of
any run; `none` is where it could not be shown.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S] [∀ n, Contains (Rg n) (S n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.WithSteps.reachUnion_outer (sys : NonlinearSysDT.WithSteps S Rg m n)
    (p : NonlinearSysDT.ReachParams) (X₀ : S n) :
    match sys.reachUnion p X₀ with
    | some R => sys.reachUnionExact p (construct X₀) ⊆ construct R
    | none => True := by -- --- PROOF ---
  cases hR : sys.reachUnion p X₀ with
  | none => trivial
  | some R =>
    intro y hy
    simp only [NonlinearSysDT.WithSteps.reachUnion] at hR
    split at hR
    case isFalse => exact absurd hR (by simp)
    case isTrue hconf =>
      -- every test passed, so each step `k < K` starts inside its certified region
      have hsub : ∀ k < p.K,
          construct (sys.sys.reach ⟨X₀, sys.U, 0, k⟩ ⟨p.o, p.ho⟩ sys.steps) ⊆ (sys.steps k).R :=
        fun k hk => (Contains.contains_sound _ _
          (List.all_eq_true.mp hconf k (List.mem_range.mpr hk))).trans (sys.region_subset k)
      obtain ⟨k, hk, x, u, traj, rfl⟩ := Set.mem_iUnion₂.mp hy
      -- the run from the bare set `construct X₀` is a run from the representation `X₀`
      have traj' : sys.sys.TrajectoryOn X₀ sys.U p.K x u := ⟨traj.init, traj.input, traj.step⟩
      have hx := sys.sys.reach_outer_on p.ho sys.steps X₀ traj'
        (sys.sys.confinement_of_subset_on p.ho sys.steps X₀ hsub traj') k hk
      rw [← Option.some_inj.mp hR]
      exact SetUnion.mem_construct.mpr ⟨_, List.mem_map_of_mem (List.mem_range.mpr
        (Nat.lt_succ_of_le hk)), hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
