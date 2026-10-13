import CORALean.ContDynamics.LinearSys.Operations.AutoTuneSearch

/-!
# `Alg. 2` lines 5-15: the step size and the truncation order for one step

[1, Alg. 2]: line 5 doubles the previous step, then `autoTuneSearch` shrinks
and `autoTuneOrder` sweeps until both admissible-error bounds clear.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] lines 5-15: `Δt_k`, `η_k`, or `none` where `fuel` halvings of `2·Δt_{k-1}`
did not suffice. -/
noncomputable def LinearSys.autoTuneDeltaT (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc Δtprev : ℝ) (ηmax fuel : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : Option (ℝ × ℕ) :=
  let Δt₀ := 2 * Δtprev                                                     -- 5. Δt_k ← 2Δt_{k-1}
  sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt₀ fuel            -- 6.-15. the repeat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
