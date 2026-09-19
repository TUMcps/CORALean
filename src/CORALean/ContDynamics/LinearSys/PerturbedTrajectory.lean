import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Two-input continuous runs: input and disturbance kept apart

`LinearSys.Trajectory` carries one signal `u`. Def. 6 and Def. 7 need a second,
independently-quantified one, `w`: `∀u(·)∈U ∃w(·)∈W` and `∃u(·)∈U ∀w(·)∈W`
cannot be built from one `Trajectory` folding `u` and `w` together, since the
quantifiers over the two differ. So this is a new structure over
`ẋ(t) = Ax(t) + u(t) + w(t)`, rather than an instance of the old one.

No `init`/`R₀`: Def. 6 and Def. 7 quantify over a single starting point `x₀`
under test, not a set of them, so `backReachSetForallExists` and its kin pin
`x 0 = x₀` themselves, the same way `reachSet` pins `x t = y` outside
`Trajectory` rather than inside it.

Like `Trajectory`, the derivative is asked for at every `t ∈ T`: stronger than
the Carathéodory concept `IntegralTrajectory` weakens to, the same
simplification `reachSet` already makes for one input.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A run under both an input `u` and a disturbance `w`, each admissible on
`T` and quantified separately by whatever calls this. -/
structure LinearSys.PerturbedTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (U W : S n)
    (x u w : ℝ → Vec ℝ n) : Prop where
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  disturbance (t : ℝ) (ht : t ∈ T) : w t ∈ construct W
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t + w t) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
