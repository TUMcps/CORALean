import CORALean.ContDynamics.LinearSys.Operations.VerifyRAIntersectionDistanceCora

/-!
# `LinearSys.verifyRAOuterVerdictCora`

The verdict of `priv_verifyRA_zonotope.m` (reached by `linearSys/verify` with `verifyAlg =
'reachavoid:zonotope'`) for one outer-approximation `Z` of the reachable set and one unsafe set
`F`, no safe set, in `ℝ¹`. `d_Fo` starts at `-Inf` (l. 64) and is set to
`aux_distanceIntersectionZono` (l. 191) where `aux_intersectionCheckFast` finds the sets
intersecting (l. 189; the LP optimum `aux_intersectionCheck` is `0` exactly where they do, so
`== 0`, ll. 606 and 609, is the intersection test in `ℝ`). The do-until loop stops at once
(l. 256, `d_Go = -Inf <= 0` and `d_Fo <= 0`) and `res = (d_Go <= 0) && (d_Fo <= 0)` (l. 280).
The refinement of `emax` and the inner approximation are not modelled: with `d_Fo = 0` the loop
ends whatever they give.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- Lines 189-195 and 280: `d_Fo` is `-Inf` (`⊥`) for disjoint sets and the distance
`aux_distanceIntersectionZono` for intersecting ones; `res = d_Fo <= 0`. -/
noncomputable def LinearSys.verifyRAOuterVerdictCora (Z F : Set ℝ) : Bool :=
  let dFo : WithBot ℝ :=                                          -- 64.  d_Fo = -Inf
    if (Z ∩ F).Nonempty then                                      -- 189. aux_intersectionCheckFast
      ((LinearSys.verifyRAIntersectionDistanceCora (Z ∩ F) : ℝ) : WithBot ℝ)  -- 191. d
    else ⊥
  if dFo ≤ 0 then true else false                                 -- 280. (d_Go <= 0) && (d_Fo <= 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
