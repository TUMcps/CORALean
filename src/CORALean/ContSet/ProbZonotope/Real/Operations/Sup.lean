import CORALean.ContSet.ProbZonotope.Real.Operations.Interval

/-!
# `ProbZonotope.sup`

CORA's `sup(probZ)` (`@probZonotope/sup.m`): the larger of the two sup-norms of the interval's
bounds, `max(‖inf I‖∞, ‖sup I‖∞)`, which its help calls `sup(‖x‖∞), x ∈ Z`. `Vec` carries the
sup norm. Taken here at the box of the confidence set, `interval`; `supCora` is CORA's, at the
box that leaves out the deterministic generators.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.sup (P : ProbZonotope n) (m : ℝ) : ℝ :=
  let I : Interval (Vec ℝ n) := P.interval m
  let N1 : ℝ := ‖I.inf‖
  let N2 : ℝ := ‖I.sup‖
  max N1 N2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
