module

public import CORALean.ContDynamics.LinearSys.Operations.TunedRun

@[expose] public section

/-!
# `Alg. 1` line 12: the reachable set

`tunedReach`: `R([0,t_f])`, the union of the first `K` iterations' time-interval sets. Line
12 unions the steps' sets, which is no zonotope, so this is a `Set`.

Nothing here clips `Δt_i` to what is left of the horizon — [1] does not either — so a run
can step past `t_f`; the accompanying theorem asks that it does not.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 12: `R([0,t_f])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def LinearSys.tunedReach (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel K : ℕ) :
    Set (Vec ℝ n) :=
  ⋃ i < K, ⋃ s ∈ sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel (i + 1), construct s.R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
