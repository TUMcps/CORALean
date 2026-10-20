module

public import CORALean.ContSet.ProbZonotope.Real.Counterexamples.UnitMeanIntervalCora

@[expose] public section

/-!
# CORA's `interval` of a probabilistic zonotope ignores the deterministic generators

`interval.m` boxes `center(probZ) ± Σ|G|` with `G = generators(probZ)`, the covariance's eigen
factor, so a probabilistic zonotope without covariance is boxed to its center: in `ℝ¹` the mean
zonotope `[-1, 1]` with covariance `0` has the mean `1`, outside the box `{0}`. The help says it
overapproximates the probabilistic zonotope.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some mean `μ` of a probabilistic zonotope lies outside CORA's interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.intervalCora_not_mem : -- --- CONCL ---
    ∃ (P : ProbZonotope 1) (μ : Vec ℝ 1),
      μ ∈ P.Z.construct ∧ μ ∉ P.intervalCora.construct := by -- --- PROOF ---
  -- the mean `1` is the generator
  refine ⟨ProbZonotope.unitMean, fun _ => 1,
    ⟨fun _ => 1, fun _ => by simp, by funext i; simp [ProbZonotope.unitMean]⟩, ?_⟩
  rw [ProbZonotope.unitMean_intervalCora]
  intro h
  have h1 : (1 : ℝ) ≤ 0 := (h 0).2
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
