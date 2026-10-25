module

public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import CORALean.ContSet.ProbZonotope.Real.Operations.Plus
public import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope

@[expose] public section

/-!
# Computing the enclosing probabilistic hulls

`[1, Alg. 1]`, line by line, from `ℛ̂([0,r])` (`Rhat`), `R̄(r)` (`Rbar`), `ℛ̲(r)` (`Runder`) and
`γ`: `ℛ̄(r) = R̄(r) ⊞ ℛ̲(r)`, `ℛ([0,r]) = ℛ̂([0,r]) + η(ℛ̄(r), γ)`, and for each `k` the loop
`ℛ([kr, (k+1)r]) = e^{Ar} ℛ([(k-1)r, kr]) + ℛ̄(r)`. The output is the result after `k`
iterations of the loop (`k = 0` is the second line); the listing's `for k = 1…ζ` and its
"`h` time intervals" are the caller's `k`. A set has no covariance, so `R̄(r)` and `η(·, γ)`
enter with covariance `0`.

## Inputs
* `sys` – system
* `r` – step size
* `Rhat` – hull of the first interval
* `Rbar` – deterministic hull of one step
* `Runder` – probabilistic part of one step
* `γ` – confidence level
* `k` – number of iterations

## Output
* the probabilistic hull after `k` iterations of the loop

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ℛ([kr, (k+1)r])` after `k` iterations of the loop of `[1, Alg. 1]`. -/
noncomputable def LinProbSys.enclosingHull (sys : LinProbSys n m) (r : ℝ)
    (Rhat : ProbZonotope n) (Rbar : Zonotope (Vec ℝ n)) (Runder : ProbZonotope n) (γ : ℝ)
    (k : ℕ) : ProbZonotope n :=
  let eAr := NormedSpace.exp (r • sys.A)
  -- 1. ℛ̄(r) = R̄(r) ⊞ ℛ̲(r)
  let Rbarbar := ProbZonotope.plus ⟨Rbar, 0⟩ Runder
  -- 2. ℛ([0,r]) = ℛ̂([0,r]) + η(ℛ̄(r), γ)
  let R₀ := ProbZonotope.plus Rhat ⟨Rbarbar.zonotope γ, 0⟩
  -- 3. for k = 1 … ζ: ℛ([kr,(k+1)r]) = e^{Ar} ℛ([(k-1)r,kr]) + ℛ̄(r)
  Nat.rec R₀ (fun _ Rk => ProbZonotope.plus (ProbZonotope.mtimes eAr Rk) Rbarbar) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
