import CORALean.ContSet.ProbZonotope.Real.Operations.IntervalCora

/-!
# `ProbZonotope.supCora`

CORA's `sup(probZ)` as the code computes it: `max(‖inf I‖∞, ‖sup I‖∞)` of `interval(probZ)`
(`intervalCora`), the box of the covariance's eigen factor around the centre, which leaves out the
deterministic generators `probZ.Z(:,2:end)`. `Theorems.SupCoraLt` is a probabilistic zonotope whose
means it does not bound.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.supCora (P : ProbZonotope n) : ℝ :=
  let I : Interval (Vec ℝ n) := P.intervalCora
  let N1 : ℝ := ‖I.inf‖
  let N2 : ℝ := ‖I.sup‖
  max N1 N2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
