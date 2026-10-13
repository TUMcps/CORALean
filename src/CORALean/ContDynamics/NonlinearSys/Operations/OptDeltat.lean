module

public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatSearch
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachSizeEstimate

@[expose] public section

/-!
# `optDeltat`: the time step size that balances the two wrapping effects

Line 10 of [1, Alg. 2], which is its §5.4, and lines 8 and 12 of [2, Alg. 2],
whose (30) and (31) are eq. (57) and eq. (58): over a finite horizon `h`
walked in `λ = ζ_δ^{-λ'}` steps, (57) estimates the size the start set reaches
and (58) minimizes it over `λ'`. Too large a step makes the set of abstraction
errors large, too small a step reduces too often; the minimum is the balance.

`λ` is the lambda binder, so eq. (57)'s `λ` is `lam` and its `λ'` is
`scalings`. `λ'_*` comes back beside `Δt*`: line 16's `estimateGain` needs it.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
noncomputable def optDeltat (le : ℝ → ℝ → Bool) (ζδ ζZ ζA φ1 r₀ rabs h : ℝ) (fuel : ℕ) :
    ℝ × ℕ :=
  let cost := reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs             -- 57. the cost function
  let sstar := optDeltatSearch le cost 0 fuel                    -- 58. the argmin over λ'
  (h * ζδ ^ sstar, sstar)                                        -- 58. Δt* = h ζ_δ^{λ'}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
