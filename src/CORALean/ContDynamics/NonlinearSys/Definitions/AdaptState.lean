import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# `Alg. 2`'s loop state

`AdaptState`: what one step of [1, Alg. 2] hands the next: its own outputs,
and the inputs those become.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What one step of [1, Alg. 2] hands the next: its own outputs, and the
inputs those become. -/
structure NonlinearSys.AdaptState (S : ℕ → Type) (n : ℕ) where
  /-- `t_k`. -/
  t : ℝ
  /-- `R(t_k)`, line 17, as line 18 reduced it. -/
  R : S n
  /-- `R(τ_k)`, line 17, as line 18 reduced it. -/
  Rτ : S n
  /-- `h_{k-1}`, the finite time horizon of the last step. -/
  h : ℝ
  /-- `φ⁽¹⁾_{k-1}`, the gain of the last step, line 16. -/
  φ : ℝ
  /-- `κ_k`, the abstraction order, line 13. -/
  κ : ℕ
  /-- `r^{(λ*)}_{abs,k'}` of the last evaluation of eq. (47). -/
  rabs : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
