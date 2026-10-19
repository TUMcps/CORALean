module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
public import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies

@[expose] public section

/-!
# `linReachAt` holds every certified run

A run on `[0, Δt]` that the linearization certifies (`LinPoint.Certifies`, the hypotheses of
`linReach_outer`: confinement to a region over which the errors hold, `u* ∈ U`, `0 ∈ Verror`,
`F⁻¹F = I`, the step admissible for `oneStep`; [1, Prop. 2]) is in the time-point set at `Δt`,
in the time-interval set and with `(x, y)` in the joint set throughout (CORA's tuning).

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
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

/-- A run certified by `L` over `[0, Δt]` is in `linReachAt`'s sets. -/
theorem NonlinDASys.IsTrajectory.linReachAt_outer {sys : NonlinDASys n p m}
    {L : NonlinDASys.LinPoint n p m}
    {Δt : ℝ} {Rinit : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n}
    {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Δt) Rinit U x y u z)
    (hΔt : 0 < Δt) {k : ℕ}
    (hc : L.Certifies sys U Δt k x y u) : -- --- CONCL ---
    x Δt ∈ (NonlinDASys.linReachAt sys L Rinit U Δt (k + 2)).1.construct ∧
      ∀ t ∈ Set.Icc 0 Δt,
        x t ∈ (NonlinDASys.linReachAt sys L Rinit U Δt (k + 2)).2.1.construct ∧
        (x t, y t)
          ∈ (NonlinDASys.linReachAt sys L Rinit U Δt (k + 2)).2.2.construct := by -- --- PROOF ---
  obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hc
  exact NonlinDASys.IsTrajectory.linReach_outer traj hΔt hF hR hL hLa hus h0 hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
