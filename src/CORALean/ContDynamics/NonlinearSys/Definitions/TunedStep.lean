module

@[expose] public section

/-!
# What the tuning of Δt hands the next step

`TunedStep`: a time step size, or the finite horizon `Δ` of [1, Alg. 2]'s first step, with the
gain `φ₁` it yields, as `tuneDeltat` and `tuneDeltatInit` return them.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A step size and its gain, over the scalar `τ`: `ℝ` for the exact layer, `𝕋` for a float
run. -/
structure NonlinearSys.TunedStep (τ : Type) where
  /-- `Δt*` of `tuneDeltat`, `Δ` of `tuneDeltatInit`. -/
  step : τ
  /-- `φ₁`, the gain of the step, by eq. (25) or (29). -/
  gain : τ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
