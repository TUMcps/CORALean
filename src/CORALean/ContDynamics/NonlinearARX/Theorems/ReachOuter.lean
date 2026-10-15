module

public import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTIsTrajectory
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# The converted system's reach contains every ARX window

`NonlinearSysDT.reach_outer` along the converted trajectory: the window of outputs
`(y(k), …, y(k+p-1))` lies in the reachable set at step `k`. The linearizations
`steps` and their regions `hR` are the caller's, as for `NonlinearSysDT`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.reach_outer (sys : NonlinearARX dy du p) {o : ℕ} (ho : 0 < o)
    {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep 𝕋 V)
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.IsTrajectory Y₀ U y u)
    (hR : ∀ k, NonlinearARX.stack p y k ∈ (steps k).R) (k : ℕ) :
    NonlinearARX.stack p y k ∈ construct
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.toNonlinearSysDT.reach_outer ho steps Y₀ (sys.toNonlinearSysDT_isTrajectory hV traj) hR k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
