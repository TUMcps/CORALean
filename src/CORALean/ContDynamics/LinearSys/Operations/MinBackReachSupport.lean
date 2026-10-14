module

public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachRun
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

@[expose] public section

/-!
# `Alg. 2` lines 12-13: one direction's support value at a step

`minBackReachSupport`: [1, Alg. 2] lines 12-13, eq. (46), `ρ(R̂^∃(-τ_k;u_j(·)), N_(j,·))`,
the step's own support value less what the direction's input trajectory takes off it.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
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

/-- Lines 12-13, eq. (46): `ρ(R̂^∃(-τ_k;u_j(·)), N_(j,·))`, the step's own support
value less what the direction's input trajectory takes off it. -/
noncomputable def LinearSys.minBackReachSupport (sys : LinearSys 𝕋 n)
    (ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (N : Mat ℝ q n) (t₀ Δt : ℝ) (η : ℕ)
    (k : ℕ) (j : Fin q) : ℝ :=
  let s := sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k
  (ρ s.R (HPolytope.rowLin N j)).val - (s.ZU₀.supportBound (-HPolytope.rowLin N j)).val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
