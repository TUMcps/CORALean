module

public import CORALean.ContDynamics.NonlinearARX.Theorems.ToNonlinearSysDTStep

@[expose] public section

/-!
# Every ARX trajectory is a trajectory of the converted system

The windows `stack p y` run through `toNonlinearSysDT` under the input signal
`feed p u`. `V` is the input set of the converted system, which must enclose every
stacked input whose `p+1` blocks all lie in `U`, hypothesis `hV`; no `ContSet`
here has a product, so the caller supplies it. The converse is not stated: a run of
the converted system need not have its window's blocks agree, nor its input be of the
form `feed p u`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.toNonlinearSysDT_trajectory (sys : NonlinearARX dy du p)
    {Y₀ : S (p * dy)} {U : S du} {V : S ((p + 1) * du)}
    (hV : ∀ v : Vec ℝ ((p + 1) * du),
      (∀ a : Fin (p + 1), (fun b => v (finProdFinEquiv (a, b))) ∈ construct U) →
        v ∈ construct V)
    {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.Trajectory Y₀ U y u) :
    sys.toNonlinearSysDT.Trajectory Y₀ V (NonlinearARX.stack p y) (NonlinearARX.feed p u) where
  init := traj.init
  input k := hV _ fun a => by
    simpa [NonlinearARX.feed] using traj.input (k + a)
  step k := sys.toNonlinearSysDT_step traj.step k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
