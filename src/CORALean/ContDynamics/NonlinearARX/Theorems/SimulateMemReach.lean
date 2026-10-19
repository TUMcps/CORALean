module

public import CORALean.ContDynamics.NonlinearARX.Theorems.ReachOuter
public import CORALean.ContDynamics.NonlinearARX.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# A simulated window lies in the reach set

`simulate_isTrajectory` composed with `reach_outer`, under the same hypotheses: the window of
simulated outputs `(y(k), …, y(k+p-1))` lies in the reachable set at step `k`.
-/

-- Authors:       Claude Sonnet 5.5
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

theorem NonlinearARX.simulate_mem_reach (sys : NonlinearARX dy du p) {o : ℕ} (ho : 0 < o)
    {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    (steps : ℕ → sys.toNonlinearSysDT.LinStep 𝕋 V)
    {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, NonlinearARX.stack p (sys.simulate y₀ u) k ∈ (steps k).R) (k : ℕ) : -- --- STMT ---
    NonlinearARX.stack p (sys.simulate y₀ u) k ∈ construct
      (sys.toNonlinearSysDT.reach ⟨Y₀, V, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.reach_outer ho hV steps (sys.simulate_isTrajectory hy₀ hu) hR k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
