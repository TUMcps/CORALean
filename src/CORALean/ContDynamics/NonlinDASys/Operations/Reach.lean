module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachLoop

@[expose] public section

/-!
# [1, Alg. 1]: reachability of a nonlinear differential-algebraic system

`reach(R(0), t_f, r, U, L_max, λ)` of `[1, Alg. 1]`: line 1's `t_0 = 0`, `L = {0}` and
`R_union = ∅`, the loop of lines 2-23 (`reachLoop`) and line 24's `Rᵈ([0, t_f]) = R_union`.
`k` is the step count of the loop, carried by `t_k`. `u* = center(U)` is the expansion point's
`u`, `taylor`'s.

## Inputs
* `sys` – system
* `taylor` – linearization of a start set
* `corollary1` – error-set computation
* `sub` – subset test
* `splitFn` – set splitting
* `R0` – start set
* `tf` – final time
* `r` – step size
* `U` – input zonotope
* `Lmax` – bound on the linearization errors
* `lam` – enlargement factor
* `η` – Taylor order
* `fuel` – iteration bound

## Output
* the union of the time-interval sets, or none

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the union `Rᵈ([0, t_f])` of the time-interval sets from the start set `R0`, or
`none` where `fuel` runs out. -/
noncomputable def NonlinDASys.reach (sys : NonlinDASys n p m)
    (taylor : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m)
    (corollary1 : NonlinDASys.LinPoint n p m → Zonotope (Vec ℝ n × Vec ℝ p) →
      Zonotope (Vec ℝ m) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p))
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (splitFn : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
    (R0 : Zonotope (Vec ℝ n)) (tf r : ℝ) (U : Zonotope (Vec ℝ m)) (Lmax : Zonotope (Vec ℝ n))
    (lam : ℝ) (η fuel : ℕ) : Option (Set (Vec ℝ n)) :=
  -- 1. `t₀ ← 0`
  let t0 : ℝ := 0
  -- 1. `L ← {0}`
  let L : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p) :=
    (Zonotope.ofPoint (0 : Vec ℝ n), Zonotope.ofPoint (0 : Vec ℝ p))
  -- 1. `R_union ← ∅`
  let Runion : Set (Vec ℝ n) := ∅
  -- 2.-24. the loop, and `Rᵈ([0, t_f]) = R_union`
  sys.reachLoop taylor corollary1 sub Lmax lam r η U splitFn fuel t0 tf R0 L Runion

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
