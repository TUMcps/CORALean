module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# `Alg. 1`'s vocabulary: the linearization bundle, the combination step, the state

`PolyTaylor`, line 3: the expansion point over the stacked `(x, u)`, and the
derivative bundle `A, w, B, D, E` no automatic differentiation here computes.
`PolyPost`, line 13: `R(ts), Rz(ts), w, A, B, D, V∆(τs), L(τs) ↦ R(t_{s+1})`.
`PolyReachState`: what one iteration of [1, Alg. 1] hands the next: `t_s`,
`R(t_s)`, `R(τs)` (line 14's last reduction, kept for the union), and the
running abstraction-error guess `Ω`, seeded once at line 1 and carried on
past line 9.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m o : ℕ}


/-- `taylor`, line 3: the expansion point over the stacked `(x, u)`, and the derivative
bundle `A, w, B, D, E` no automatic differentiation here computes. -/
abbrev NonlinearSys.PolyTaylor (n m o : ℕ) := PolyZonotope (Vec ℝ n) →
  Vec ℝ o × Mat ℝ n n × Vec ℝ n × Mat ℝ n m × (Fin n → Mat ℝ o o) × (Fin n → Fin o → Mat ℝ o o)

/-- `post`, line 13: `R(ts), Rz(ts), w, A, B, D, V∆(τs), L(τs) ↦ R(t_{s+1})`. -/
abbrev NonlinearSys.PolyPost (n m o : ℕ) := PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ o) →
  Vec ℝ n → Mat ℝ n n → Mat ℝ n m → (Fin n → Mat ℝ o o) → PolyZonotope (Vec ℝ n) →
  Real.Interval (Vec ℝ n) → PolyZonotope (Vec ℝ n)


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next: `t_s`, `R(t_s)`, `R(τs)` (line 14's
last reduction, kept for the union), and the running abstraction-error guess `Ω`, seeded
once at line 1 and carried on past line 9. -/
structure NonlinearSys.PolyReachState (n : ℕ) where
  /-- `t_s`, line 16. -/
  t : ℝ
  /-- `R(t_s)`, lines 1, 6, 11, 13. -/
  R : PolyZonotope (Vec ℝ n)
  /-- `R(τs)`, line 7, for `R_union` at line 15. -/
  Rτ : PolyZonotope (Vec ℝ n)
  /-- `Ω(s)`, lines 1, 5, 9-10. -/
  Ω : PolyZonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
