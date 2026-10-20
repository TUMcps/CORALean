module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinDASys.Theorems.IsTrajectoryToNonlinearSys
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter

@[expose] public section

/-!
# The float differential-algebraic run encloses every trajectory

Where `fm` encloses the reduced system, the differential variable of every trajectory of the
algebraic system on `[0, tFinal - tStart]` from `X₀` under inputs in `U` is, at every time of
window `k`, in the `k`-th set `NonlinDASys.reachFloat` returns. An outer statement.

## Inputs
* `sys` – system
* `red` – reduced ordinary model
* `fm` – float model of the reduced system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Hypotheses
* `h` – the float model encloses the reduced system

## Conclusion
* every trajectory's differential state lies in the returned window sets
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.reachFloat_outer {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {fm : NonlinearSys.FloatModel 𝕋 n m} (h : fm.Encloses red.toNonlinearSys)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ NonlinDASys.reachFloat red fm params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
        {z : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
            params.U.construct x y u z →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (hR : NonlinDASys.reachFloat red fm params options = some Rs)
  obtain ⟨N, hN, hlen, hout⟩ := h.reachFloat_outer _ hR
  exact ⟨N, hN, hlen, fun {x y u z} traj => hout (traj.toNonlinearSys red)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
