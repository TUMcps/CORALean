module

public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachPostCov
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryCovariance

@[expose] public section

/-!
# The reach loop carries the covariance of every run

From `initReach`'s `options`, after `k` steps of `post` with its `pRinput`, the covariance of the
set `post` returns is that of the state of every `LinProbSys.IsTrajectory` at `r + k r`, on a
`T` that holds that time: both are `Σ_s(r + k r)`, the loop's by `initReach_post_cov` and the
run's by `IsTrajectory.covariance_eq`. For a diagonalizable `A` given as its eigendecomposition.
The covariance, not the law: the means `post` carries have no statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix MeasureTheory ProbabilityTheory ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cov[x_i(r + k r), x_j(r + k r)]` is entry `(i, j)` of the covariance of `post`'s set after
`k` steps from `initReach`. -/
theorem LinProbSys.IsTrajectory.initReach_post_cov (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (hV : IsUnit Veig.det) (hA : sys.A = Veig * diagonal lambda * Veig⁻¹)
    (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m)) (uTrans : Vec ℝ m)
    {r : ℝ} (hr : 0 ≤ r) (η : ℕ) (gamma : ℝ) (originContained : Bool) (k : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : S n} {U' : S m} {x₀ : Vec ℝ n}
    {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n} (traj : sys.IsTrajectory P T X₀ U' x₀ u x)
    (hT : r + k * r ∈ T) (i j : Fin n) : -- --- STMT ---
    let out := sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma originContained
    cov[fun ω => x (r + k * r) ω i, fun ω => x (r + k * r) ω j; P]
      = (sys.post r out.2.2.2 ((fun st => (sys.post r out.2.2.2 st).1)^[k] out.2.2.1)).2.cov i j
      := by -- --- PROOF ---
  intro out
  rw [(sys.initReach_post_cov Veig lambda hV hA Rinit gammaInit U uTrans r η gamma
    originContained k).2]
  exact traj.covariance_eq hT (by positivity) i j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
