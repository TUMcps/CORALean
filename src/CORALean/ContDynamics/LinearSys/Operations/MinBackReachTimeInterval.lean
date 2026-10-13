module

public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachP
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs

@[expose] public section

/-!
# `Alg. 1` line 16: the minimal time-interval backward reachable set

`minBackReachTimeInterval`: [1, Alg. 1] line 16, `R^{∀∃}(-τ)`, the `ω` steps' sets united,
each cut by the polytope `⟨N,p⟩_H` the propagated support functions built, over the
time-inverted dynamics `ẋ̃ = -A x̃ - u - w`. Nothing here searches, so no fuel: `ω` and `η`
are fixed by [1, Assumption 1] and the loop is bounded by `ω`.

`ρ` is the caller's support oracle for a constrained zonotope — a linear program, which
`HPolytope.supportBound` solves but only as an `Option`. `Zw` is (26), the constant centre
trajectory's contribution over one interval. And line 16's union is no constrained zonotope,
so the result is a `Set`, as `tunedReach` returns one for the same reason.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n q : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 16: `R̂^∀∃(-τ)`, the `ω` steps' sets united, each cut by the
polytope `⟨N,p⟩_H` the propagated support functions built. -/
noncomputable def LinearSys.minBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  let Δt := (tend - t₀) / ω                                         -- 1. Δt ← (t_end - t₀)/ω
  let P := HPolytope.ineqs N                                        -- 4., 14. ⟨N,p⟩_H
    (sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η (ω - 1))
  ⋃ k < ω, ((sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k).R.construct ∩ P.construct)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
