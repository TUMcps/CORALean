import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachRun

/-!
# `Alg. 2` line 14: the maximal time-interval backward reachable set

`maxBackReachTimeInterval`: [1, Alg. 2] line 14, `R̂^{∃∀}(-τ)`, the union of the `ω`
iterations' inner approximated time-interval solutions. Nothing here searches, so no fuel:
`ω` and `η` are fixed by [1, Assumption 1] and the loop is bounded by `ω`.

Three departures, all inherited from the pieces this assembles. `P₁`, `P₂` are supplied rather
than computed inside, as `CZ` is to `Alg. 1`. (22)'s `‖·‖₂` is the spectral norm and this
tree's matrices carry the ℓ^∞ operator norm, so `maxBackReachMu` takes the Frobenius norm,
which dominates it. And line 14's union is no constrained zonotope, so the result is a `Set`,
as in `Alg. 1`.

`ρ` is the caller's support oracle for a polytope — the linear program of (9). `Zw` is (26),
the constant centre trajectory's contribution over one interval.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 14: `R̂^{∃∀}(-τ)`, the union of the `ω` iterations' inner
approximated time-interval solutions. -/
noncomputable def LinearSys.maxBackReachTimeInterval (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  let Δt := (tend - t₀) / ω                                         -- 1. Δt ← (t_end - t₀)/ω
  ⋃ k < ω, (sys.maxBackReachRun ρ P₁ P₂ U W₀ Zw t₀ Δt η (k + 1)).R.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
