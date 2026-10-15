module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter

@[expose] public section

/-!
# `reach` contains every trajectory known only up to a bound

`LinearSysDT.reach_outer_on`'s induction, unpacking `traj.step`'s existential
for the `A` and the membership `reach_one_outer` now asks for, in place of
reading `toRealMat sys.A` straight off the equation.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it. -/
theorem LinParamSysDT.reach_outer_on (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    {K : ℕ} {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectoryOn R₀ U K x u) :
    ∀ k ≤ K, x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    obtain ⟨A, hA, hstep⟩ := traj.step k hkK
    show x (k + 1) ∈ construct (sys.reach ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩, U, 0, 1⟩ ⟨o, ho⟩)
    rw [hstep]
    exact sys.reach_one_outer ho _ _ hA (ih hkK.le) (traj.input k hkK)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
