module

public import CORALean.ContSet.ProbZonotope.Real.Operations.UnitMean
public import CORALean.ContSet.ProbZonotope.Real.Counterexamples.IntervalCora
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GeneratorsMulTranspose

@[expose] public section

/-!
# CORA's `interval` of `[-1, 1]` with no covariance is the origin

Its probabilistic generators are `0` (a zero covariance has the factor `G Gᵀ = 0`, so `G = 0`), and
`interval.m` boxes the center `0` by `Σ|G| = 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `interval` of `[-1, 1]` with no covariance is the origin
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_unitMean_generators : ProbZonotope.unitMean.generators = 0 := by
  -- `G Gᵀ = 0` forces `G = 0`
  have h := ProbZonotope.unitMean.generators_mul_transpose Matrix.PosSemidef.zero
  exact Matrix.self_mul_conjTranspose_eq_zero.1 (by simpa [ProbZonotope.unitMean] using h)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.unitMean_intervalCora : ProbZonotope.unitMean.intervalCora = ⟨0, 0⟩ := by
  -- both bounds are the center `0`
  unfold ProbZonotope.intervalCora
  rw [aux_unitMean_generators]
  refine congrArg₂ Interval.mk ?_ ?_ <;> funext i <;> simp [ProbZonotope.unitMean]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
