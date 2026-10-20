module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRun

@[expose] public section

/-!
# `Alg. 3` line 14: the EA time-interval backward reachable set

`maxBackReachTimeInterval`: [1, Alg. 3] line 14, `R̂^{∃∀}(-τ)`, the union of the `ω` iterations'
inner approximated time-interval solutions. Nothing here searches, so no fuel: `ω` and `η` are
fixed by [1, Assumption 1] and the loop is bounded by `ω`. Lines 1-2 and 6-14 of it: the two
polytopes `P₁`, `P₂` of lines 3-5 are taken here, and `LinearSys.maxBackReach` is the whole
listing. Line 14's union is no constrained zonotope, so the result is a `Set`, as in `Alg. 2`.
`ρ` is the caller's support oracle for a polytope, the linear program of (9). `Zw` is (27), the
constant center trajectory's contribution over one interval.

## Inputs
* `sys` – linear system
* `P₁` – first eroded polytope
* `P₂` – second eroded polytope
* `U` – input zonotope
* `W₀` – initial disturbance zonotope
* `Zw` – center trajectory contribution
* `t₀` – start time
* `tend` – end time
* `η` – Taylor order
* `ω` – number of iterations

## Hypotheses
* `ρ` – support oracle for polytopes

## Output
* union of the iterations' inner approximated time-interval solutions

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] line 14: `R̂^{∃∀}(-τ)`, the union of the `ω` iterations' inner
approximated time-interval solutions. -/
noncomputable def LinearSys.maxBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  -- 1. Δt ← (t_end - t₀)/ω
  let Δt := (tend - t₀) / ω
  ⋃ k < ω, (sys.maxBackReachRun ρ P₁ P₂ U W₀ Zw t₀ Δt η (k + 1)).R.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
