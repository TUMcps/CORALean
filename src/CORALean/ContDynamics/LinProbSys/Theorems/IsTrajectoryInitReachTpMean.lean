module

public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTpOuter
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryIntegral
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryMeanSplit

@[expose] public section

/-!
# The time-point set of `initReach` encloses the mean of every run

For every `LinProbSys.IsTrajectory` from a point of `Rinit`'s zonotope of means under inputs in
CORA's `U + uTrans` [1], on a `T` that holds the first step `[0, r]`, the expectation of the
state at `r` lies in the set of `Rfirst.tp`: the mean of the run is the one of
`initReach_tp_outer` (`IsTrajectory.integral_eq`, `IsTrajectory.mean_eq_add_inputReach`). The
hypotheses are those of `initReach_tp_outer`. Only the mean; the probability is
`IsTrajectory.initReach_tp_prob`.

## References

* [1] `contDynamics/@linProbSys/initReach.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `E[x(r)] ∈ Rfirst.tp` for every run from `Rinit` under inputs in `U + uTrans`. -/
theorem LinProbSys.IsTrajectory.initReach_tp_mean (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m))
    (uTrans : Vec ℝ m) {r : ℝ} (hr : 0 < r) {η : ℕ}
    (hε : ‖r • sys.A‖ / ((η : ℝ) + 2) < 1) (gamma : ℝ) (originContained : Bool)
    (hA : IsUnit sys.A.det) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ}
    {x₀ : Vec ℝ n} {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n}
    (traj : sys.IsTrajectory (S := 𝒵) P T Rinit.Z (U.plus (Zonotope.ofPoint uTrans)) x₀ u x)
    (hT : Set.Icc 0 r ⊆ T) : -- --- STMT ---
    ∫ ω, x r ω ∂P ∈ (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
      originContained).1.Z.construct := by -- --- PROOF ---
  rw [traj.integral_eq (hT ⟨hr.le, le_rfl⟩) hr.le]
  obtain ⟨w, hw, heq⟩ := traj.mean_eq_add_inputReach hr.le hT
  rw [heq]
  exact sys.initReach_tp_outer Veig lambda Rinit gammaInit U uTrans hr hε gamma originContained hA
    traj.init hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
