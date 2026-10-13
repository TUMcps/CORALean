import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval

/-!
# `ProbZonotope.interval`

The interval hull of the confidence set, `interval(zonotope(probZ, m))`: the box that
`@probZonotope/interval.m` says it computes, "overapproximates a probabilistic zonotope by an
interval". CORA's code boxes only the covariance's eigen factor around the centre and drops the
deterministic generators (`intervalCora`); the confidence set `Z ⊕ m g [-1, 1]ⁿ` carries both,
and every law puts probability at least `erf(m/√2)ⁿ` on its box (`Theorems.IntervalProb`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.interval (P : ProbZonotope n) (m : ℝ) : Interval (Vec ℝ n) :=
  (P.zonotope m).interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
