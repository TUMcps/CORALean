import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateTrajectory

/-!
# A simulated window lies in the reach set

`simulate_trajectory` composed with `reach_outer`, under the same hypotheses: the window of
simulated outputs `(y(k), …, y(k+p-1))` lies in the reachable set at step `k`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.simulate_mem_reach (sys : NonlinearARX dy du p) {o : ℕ} (ho : 0 < o)
    {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep V)
    {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, NonlinearARX.stack p (sys.simulate y₀ u) k ∈ (steps k).R) (k : ℕ) :
    NonlinearARX.stack p (sys.simulate y₀ u) k ∈ construct
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.reach_outer ho hV steps (sys.simulate_trajectory hy₀ hu) hR k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
