import CORALean.ContDynamics.LinearSys.Operations.MinBackReachSupport

/-!
# `Alg. 1` lines 4 and 14: the accumulated support value

`minBackReachP`: [1, Alg. 1] lines 4 and 14, `p_(j)` after the steps `0` to `k`. `max`, not
line 14's `min` — a union's support is the largest of its parts', see the findings on the
reference page.

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

/-- Lines 4 and 14: `p_(j)` after the steps `0` to `k`. `max`, not line 14's
`min` — a union's support is the largest of its parts', see the findings. -/
noncomputable def LinearSys.minBackReachP (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ) : ℕ → Fin q → ℝ
  | 0 => fun j => sys.minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η 0 j
  | k + 1 => fun j => max (sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η k j)
      (sys.minBackReachSupport ρ CZ W₀ U₀ Zw N t₀ Δt η (k + 1) j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
