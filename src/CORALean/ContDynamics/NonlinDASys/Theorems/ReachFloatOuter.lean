import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToNonlinearSys
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter

/-!
# The float differential-algebraic run encloses every trajectory

Where `fm` encloses the reduced system, the differential variable of every trajectory of the
algebraic system on `[0, tFinal - tStart]` from `X₀` under inputs in `U` is, at every time of
window `k`, in the `k`-th set `NonlinDASys.reachFloat` returns. An outer statement.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.reachFloat_outer {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {fm : NonlinearSys.FloatModel 𝕋 n m} (h : fm.Encloses red.toNonlinearSys)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rs : List (Zonotope (Vec 𝕋 n))}
    (hR : NonlinDASys.reachFloat red fm params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m},
        sys.Trajectory (S := fun k => Set (Vec ℝ k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          params.U.construct x y u →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
          (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by
  obtain ⟨N, hN, hlen, hout⟩ := h.reachFloat_outer hR
  exact ⟨N, hN, hlen, fun {x y u} traj => hout (traj.toNonlinearSys red)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
