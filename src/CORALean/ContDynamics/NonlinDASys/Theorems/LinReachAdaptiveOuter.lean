module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.AdaptPassLinPoint
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachAtOuter

@[expose] public section

/-!
# An accepted adaptive pass holds every certified run

The sets of an accepted `linReachAdaptive` pass are `linReach` at the linearization and the
errors the pass settled on, at the step size it chose ([1, Prop. 2]); so `linReach_outer`
(`linReachAt_outer`) is its outer theorem. The tuning cannot affect it: it enters only through
the `Δt` and the errors the certificate is asked of. `abstractionErrorAdaptive_outer` is the
certificate's remainder part, with the Hessian intervals holding over the region.

## Inputs
* `sys` – system
* `T` – tuning heuristics
* `Rstart` – start set
* `U` – input zonotope
* `fuelErr` – error loop fuel
* `fuelHalf` – step halving fuel
* `adm_x` – admissible state errors
* `adm_y` – admissible algebraic errors
* `k` – Taylor order minus two
* `h` – horizon
* `lastStep` – whether this is the last step
* `pass` – accepted pass
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal

## Hypotheses
* `_hpass` – the adaptive step returned `pass`
* `traj` – DAE trajectory
* `hΔt` – pass step positive
* `hc` – the linearization certifies the run

## Conclusion
* the run lies in the sets of the accepted pass

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
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

/-- An accepted pass of `linReachAdaptive`: a run certified by its errors at its step size is in
its sets. -/
theorem NonlinDASys.IsTrajectory.linReachAdaptive_outer {sys : NonlinDASys n p m}
    {T : NonlinDASys.AdaptTuning n p m q} {Rstart : Zonotope (Vec ℝ n)}
    {U : Zonotope (Vec ℝ m)} {fuelErr fuelHalf : ℕ} {adm_x : Vec ℝ n} {adm_y : Vec ℝ p}
    {k : ℕ} {h : ℝ} {lastStep : Bool} {pass : NonlinDASys.AdaptPass n p}
    (_hpass : sys.linReachAdaptive T Rstart U (k + 2) fuelErr fuelHalf adm_x adm_y h lastStep
      = some pass) {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 pass.Δt) Rstart U x y u z)
    (hΔt : 0 < pass.Δt)
    (hc : (pass.linPoint (T.taylor Rstart)).Certifies sys U pass.Δt k x y u) : -- --- CONCL ---
    let lr := NonlinDASys.linReachAt sys (pass.linPoint (T.taylor Rstart)) Rstart U pass.Δt (k + 2)
    x pass.Δt ∈ lr.1.construct ∧
      ∀ t ∈ Set.Icc 0 pass.Δt,
        x t ∈ lr.2.1.construct ∧
        (x t, y t) ∈ lr.2.2.construct := by -- --- PROOF ---
  intro lr
  exact traj.linReachAt_outer hΔt hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
