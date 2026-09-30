import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn

/-!
# Confinement, discharged from the computed sets

`reach_outer_on` asks for confinement (`x j ∈ (steps j).R`) at every step
strictly *below* `K` to place `x K` — never at `K` itself. That asymmetry is
what makes this theorem possible without circularity: strong induction on `k`
gets confinement below `k` from the induction hypothesis, places `x k` inside
`reach ... k` by `reach_outer_on`, and `hsub k` — the computed set contained
in the candidate region — turns that placement into confinement *at* `k`,
with confinement at `K` itself never assumed.

`hsub` is a hypothesis about sets, not a decision procedure: nothing here
makes membership or subset checkable, and for a general `R : Set (Vec ℝ n)`
it is not. What changes is *what* a caller must establish — a checkable
property of the computed enclosures, rather than of every trajectory.

CORA also *enlarges* the candidate region on failure and retries; that search
owes no proof here, exactly as `ConPolyZono.reduceBy_outer` is sound at every
partition without picking one. No search is implemented.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Confinement at every step, discharged from the computed sets: a caller
checks `hsub`, that each step's computed reachable set lies inside its own
certified region, instead of assuming confinement of the trajectory. -/
theorem NonlinearSysDT.confinement_of_subset (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep U) (R₀ : S n)
    (hsub : ∀ k, construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) ⊆ (steps k).R)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ (steps k).R := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hOn : sys.TrajectoryOn R₀ U k x u :=
      ⟨traj.init, fun j _ => traj.input j, fun j _ => traj.step j⟩
    exact hsub k (sys.reach_outer_on ho steps R₀ hOn ih k le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
