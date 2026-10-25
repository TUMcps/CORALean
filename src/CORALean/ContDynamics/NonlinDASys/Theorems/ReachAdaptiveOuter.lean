module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptive
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachAdaptiveLoopOuter

@[expose] public section

/-!
# `reachAdaptive` holds every certified run

`reachAdaptiveLoop_outer` from the start state of `reachAdaptive` ([1, Alg. 1]): a certified
run is in the union returned, up to the time reached.

## Inputs
* `sys` – system
* `T` – tuning heuristics
* `U` – input zonotope
* `tFinal` – final time
* `tol` – tolerance
* `h₀` – initial step size
* `adm_x₀` – admissible state errors
* `adm_y₀` – admissible algebraic errors
* `k` – Taylor order minus two
* `fuelErr` – error loop fuel
* `fuelHalf` – step halving fuel
* `fuel` – iteration bound
* `R0` – start set
* `Tmax` – horizon of the trajectory
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal
* `res` – returned union
* `tEnd` – time reached

## Hypotheses
* `traj` – DAE trajectory
* `hT` – final time within the horizon
* `hcert` – every adaptive pass certifies the run
* `h0` – final time nonnegative
* `hres` – the algorithm returned `res` and `tEnd`
* `hpos` – time reached positive

## Conclusion
* the run up to the time reached lies in the returned union

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach_adaptive`: a certified run is in the union returned, up to the time reached. -/
theorem NonlinDASys.reachAdaptive_outer (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (U : Zonotope (Vec ℝ m)) (tFinal tol h₀ : ℝ)
    (adm_x₀ : Vec ℝ n) (adm_y₀ : Vec ℝ p) (k fuelErr fuelHalf fuel : ℕ)
    {R0 : Zonotope (Vec ℝ n)} {Tmax : ℝ} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Tmax) R0 U x y u z)
    (hT : tFinal ≤ Tmax)
    (hcert : ∀ (st : NonlinDASys.AdaptState n p) (h : ℝ) (lastStep : Bool)
      (pass : NonlinDASys.AdaptPass n p), 0 ≤ st.t → x st.t ∈ st.R.construct →
      sys.linReachAdaptive T st.R U (k + 2) fuelErr fuelHalf st.adm_x st.adm_y h lastStep
        = some pass → 0 < pass.Δt → pass.Δt ≤ tFinal - st.t →
      (pass.linPoint (T.taylor st.R)).Certifies sys U pass.Δt k
        (fun s => x (st.t + s)) (fun s => y (st.t + s)) (fun s => u (st.t + s)))
    (h0 : 0 ≤ tFinal) {res : Set (Vec ℝ n)} {tEnd : ℝ}
    (hres : sys.reachAdaptive T R0 U tFinal tol h₀ adm_x₀ adm_y₀ (k + 2) fuelErr fuelHalf fuel
      = some (res, tEnd)) (hpos : 0 < tEnd) : -- --- CONCL ---
    ∀ t ∈ Set.Icc 0 tEnd, x t ∈ res := by -- --- PROOF ---
  refine NonlinDASys.reachAdaptiveLoop_outer sys T U tFinal tol k fuelErr fuelHalf traj hT hcert
    fuel _ ∅ le_rfl traj.init (fun h => absurd h (lt_irrefl 0)) h0 res tEnd hres hpos

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
