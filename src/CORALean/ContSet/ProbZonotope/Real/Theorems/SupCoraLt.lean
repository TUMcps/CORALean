module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.UnitMeanIntervalCora
public import CORALean.ContSet.ProbZonotope.Real.Operations.SupCora

@[expose] public section

/-!
# CORA's `sup` of a probabilistic zonotope is below the norm of a mean

`sup.m` takes its norms from `interval`, which ignores the deterministic generators: for the mean
zonotope `[-1, 1]` with covariance `0` it returns `0`, while the means reach norm `1`. The help says
`sup(‖x‖∞), x ∈ Z`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.supCora_lt :
    ∃ (P : ProbZonotope 1) (μ : Vec ℝ 1), μ ∈ P.Z.construct ∧ P.supCora < ‖μ‖ := by
  -- the mean `1` is the generator, of norm `1`
  refine ⟨ProbZonotope.unitMean, fun _ => 1,
    ⟨fun _ => 1, fun _ => by simp, by funext i; simp [ProbZonotope.unitMean]⟩, ?_⟩
  simp [ProbZonotope.supCora, ProbZonotope.unitMean_intervalCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
