import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTTrajectory
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter

/-!
# The converted system's reach contains every ARX window

`NonlinearSysDT.reach_outer` along the converted trajectory: the window of outputs
`(y(k), …, y(k+p-1))` lies in the reachable set at step `k`. The linearizations
`steps` and their regions `hR` are the caller's, as for `NonlinearSysDT`.
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

theorem NonlinearARX.reach_outer (sys : NonlinearARX dy du p) {o : ℕ} (ho : 0 < o)
    {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep V)
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.Trajectory Y₀ U y u)
    (hR : ∀ k, NonlinearARX.stack p y k ∈ (steps k).R) (k : ℕ) :
    NonlinearARX.stack p y k ∈ construct
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.toNonlinearSysDT.reach_outer ho steps Y₀ (sys.toNonlinearSysDT_trajectory hV traj) hR k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
