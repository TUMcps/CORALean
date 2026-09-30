import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn

/-!
# Confinement of a bounded run, discharged from the computed sets

`confinement_of_subset` for a run known only up to step `K`: the same strong
induction, each step `k < K` placed inside `reach ... k` by `reach_outer_on`
from confinement strictly below `k`, then inside `(steps k).R` by `hsub k`.
Only the sets below `K` are asked about, which is exactly what `reachUnion`
tests at run time: the set step `K` ends in starts no step of the horizon.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Confinement below `K` of a run known up to `K`, from each step's computed
set lying inside that step's certified region. -/
theorem NonlinearSysDT.confinement_of_subset_on (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep U) (R₀ : S n) {K : ℕ}
    (hsub : ∀ k < K, construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) ⊆ (steps k).R)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (traj : sys.TrajectoryOn R₀ U K x u) :
    ∀ k < K, x k ∈ (steps k).R := by -- --- PROOF ---
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    -- the run up to `k`, confined below `k` by the induction hypothesis
    have hOn : sys.TrajectoryOn R₀ U k x u :=
      ⟨traj.init, fun j hj => traj.input j (hj.trans hk), fun j hj => traj.step j (hj.trans hk)⟩
    exact hsub k hk
      (sys.reach_outer_on ho steps R₀ hOn (fun j hj => ih j hj (hj.trans hk)) k le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
