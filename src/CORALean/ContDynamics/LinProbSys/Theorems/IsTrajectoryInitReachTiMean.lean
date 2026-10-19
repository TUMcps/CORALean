module

public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTiOuter
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryIntegral
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryMeanSplit

@[expose] public section

/-!
# The time-interval set of `initReach` encloses the mean of every run over the first step

For every `LinProbSys.IsTrajectory` from a point of `Rinit`'s zonotope of means under inputs in
CORA's `U + uTrans` [1], on a `T` that holds the first step `[0, r]`, the expectation of the
state at every `t ∈ [0, r]` lies in the set of `Rfirst.ti`: the mean of the run is the one of
`initReach_ti_outer` (`IsTrajectory.integral_eq`, `IsTrajectory.mean_eq_add_inputReach`). The
hypotheses are those of `initReach_ti_outer`. Only the mean: that the state is in the set with
the probability of its confidence part is not proved, see
`references/coverage/contDynamics/linProbSys.md`, row `initReach`.

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

/-- `E[x(t)] ∈ Rfirst.ti` for every `t ∈ [0, r]` and every run from `Rinit` under inputs in
`U + uTrans`. -/
theorem LinProbSys.IsTrajectory.initReach_ti_mean (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m))
    (uTrans : Vec ℝ m) {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hε : ‖r • sys.A‖ / (((k + 2 : ℕ) : ℝ) + 2) < 1) (gamma : ℝ) (originContained : Bool)
    (hA : IsUnit sys.A.det) (hoc : originContained = true → sys.B *ᵥ uTrans = 0)
    (h0 : (0 : Vec ℝ m) ∈ U.construct) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : Set ℝ} {x₀ : Vec ℝ n} {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n}
    (traj : sys.IsTrajectory (S := 𝒵) P T Rinit.Z (U.plus (Zonotope.ofPoint uTrans)) x₀ u x)
    (hT : Set.Icc 0 r ⊆ T) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- STMT ---
    ∫ ω, x t ω ∂P ∈ (sys.initReach Veig lambda Rinit gammaInit U uTrans r (k + 2) gamma
      originContained).2.1.Z.construct := by -- --- PROOF ---
  rw [traj.integral_eq (hT ⟨ht0, htr⟩) ht0]
  obtain ⟨w, hw, heq⟩ := traj.mean_eq_add_inputReach ht0
    ((Set.Icc_subset_Icc le_rfl htr).trans hT)
  rw [heq]
  exact sys.initReach_ti_outer Veig lambda Rinit gammaInit U uTrans hr hε gamma originContained hA
    hoc h0 traj.init ht0 htr hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
