import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet

/-!
# `reachSet` contains every trajectory

The same statement as `reach_outer`, one layer down: the induction step is the
dynamics themselves rather than three class guarantees, since `reachSet` is
built from the step and nothing else. So this holds at a representation with no
`plus`, no `mtimes` and no `reduce` — none is mentioned.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachSet_outer (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ sys.reachSet R₀ U k := by -- --- PROOF ---
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ mulVecLin (toRealMat sys.A) '' sys.reachSet R₀ U k + construct U
    rw [traj.step k]
    exact Set.add_mem_add ⟨x k, ih, rfl⟩ (traj.input k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
