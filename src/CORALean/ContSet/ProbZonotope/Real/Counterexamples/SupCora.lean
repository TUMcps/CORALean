module

public import CORALean.ContSet.ProbZonotope.Real.Counterexamples.IntervalCora
public import CORALean.ContSet.ProbZonotope.Real.Counterexamples.UnitMeanIntervalCora

@[expose] public section

/-!
# `ProbZonotope.supCora`

CORA's `sup(probZ)` as the code computes it: `max(‖inf I‖∞, ‖sup I‖∞)` of `interval(probZ)`
(`intervalCora`), the box of the covariance's eigen factor around the center, which leaves out the
deterministic generators `probZ.Z(:,2:end)`. `Theorems.SupCoraLt` is a probabilistic zonotope whose
means it does not bound.

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

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
noncomputable def ProbZonotope.supCora (P : ProbZonotope n) : ℝ :=
  let I : Interval (Vec ℝ n) := P.intervalCora
  let N1 : ℝ := ‖I.inf‖
  let N2 : ℝ := ‖I.sup‖
  max N1 N2

end CORALean.Real

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
