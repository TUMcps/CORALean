import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachRunFloatOuter
import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

/-!
# `reachAlgFloat` holds every run of the real system over every window

The counterpart of `FloatModel.Encloses.reachFloat_outer` at either `alg`, against the
same object: every run of `ẋ = f(x, u)` on `[0, tFinal - tStart]` from `X₀` under any
input signal in `U`. `Reach.steps` makes the horizon `N` steps exactly, and
`linReachRunFloat_outer` does the rest.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order, every run on `[0, tFinal - tStart]` from
`X₀` under inputs in `U` is, at every time of window `k`, in the `k`-th set returned. -/
theorem NonlinearSys.FloatHessModel.Encloses.reachAlgFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {alg : NonlinearSys.LinReachAlg}
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rs : List (Zonotope (Vec 𝕋 n))}
    (hR : fm.reachAlgFloat alg params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.timeStep = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
        sys.Trajectory (S := fun k => Set (Vec ℝ k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.R0.construct
          params.U.construct x u →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.timeStep)
          (((k : ℝ) + 1) * toReal options.timeStep), x t ∈ Rs[k].construct := by -- --- PROOF ---
  unfold NonlinearSys.FloatHessModel.reachAlgFloat at hR
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨N, hN, hrun⟩ := hR
  obtain ⟨-, hNΔt⟩ := Reach.steps_spec_toReal hN
  obtain ⟨hlen, hout⟩ := h.linReachRunFloat_outer N hrun
  refine ⟨N, hNΔt, hlen, fun {x u} traj => ?_⟩
  -- the horizon is `N` steps exactly
  rw [← hNΔt] at traj
  exact hout traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
