module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `Alg. 2`'s loop state

`AdaptState`: what one step of [1, Alg. 2] hands the next: its own outputs,
and the inputs those become.

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What one step of [1, Alg. 2] hands the next: its own outputs, and the
inputs those become. The time `T` and the scalar `τ` of the tuning quantities are
`ℝ` for the exact layer; a float run keeps `t_k` exactly in `ℚ` and the rest in `𝕋`. -/
structure NonlinearSys.AdaptState (S : ℕ → Type) (n : ℕ) (T : Type := ℝ) (τ : Type := ℝ) where
  /-- `t_k`. -/
  t : T
  /-- `R(t_k)`, line 17, as line 18 reduced it. -/
  R : S n
  /-- `R(τ_k)`, line 17, as line 18 reduced it. -/
  Rτ : S n
  /-- `h_{k-1}`, the finite time horizon of the last step. -/
  h : τ
  /-- `φ⁽¹⁾_{k-1}`, the gain of the last step, line 16. -/
  φ : τ
  /-- `κ_k`, the abstraction order, line 13. -/
  κ : ℕ
  /-- `r^{(λ*)}_{abs,k'}` of the last evaluation of eq. (47). -/
  rabs : τ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
