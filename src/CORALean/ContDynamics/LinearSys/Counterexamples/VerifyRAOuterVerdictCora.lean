module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `LinearSys.verifyRAIntersectionDistanceCora`

CORA's `aux_distanceIntersectionZono` in `@linearSys/private/priv_verifyRA_zonotope.m`:
`w = rad(interval(conZonotope(Z) & P)); dist = 2*sqrt(sum(w.^2))`, the `2`-norm of the diameter of
the interval hull of the intersection. Here in `ℝ¹`, where the interval hull of a set `S` is
`[inf S, sup S]` and `rad` its half-width.

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

# CORA's `reachavoid:zonotope` verifies a set touching the unsafe set

`d_Fo <= 0` (`priv_verifyRA_zonotope.m` l. 280) accepts `d_Fo = 0`, which is what
`aux_distanceIntersectionZono` returns when the outer approximation meets the unsafe set in a
single point. For `ẋ = 0` from `X₀ = [-1, 1]` (the reachable set is `X₀`, so `Z = [-1, 1]`) and the
unsafe set `x ≥ 1`, the reachable state `1` is unsafe, yet the verdict is `true`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the verdict is true although a reachable state lies in the unsafe set
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `aux_distanceIntersectionZono` in `ℝ¹`: `2 * sqrt (w ^ 2)` for `w` the radius of the interval
hull `[inf S, sup S]` of the intersection `S`. -/
noncomputable def LinearSys.verifyRAIntersectionDistanceCora (S : Set ℝ) : ℝ :=
  let w := (sSup S - sInf S) / 2                                  -- w = rad(interval(Z & P))
  2 * Real.sqrt (w ^ 2)                                           -- dist = 2*sqrt(sum(w.^2))


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- Lines 189-195 and 280: `d_Fo` is `-Inf` (`⊥`) for disjoint sets and the distance
`aux_distanceIntersectionZono` for intersecting ones; `res = d_Fo <= 0`. -/
noncomputable def LinearSys.verifyRAOuterVerdictCora (Z F : Set ℝ) : Bool :=
  let dFo : WithBot ℝ :=                                          -- 64.  d_Fo = -Inf
    if (Z ∩ F).Nonempty then                                      -- 189. aux_intersectionCheckFast
      ((LinearSys.verifyRAIntersectionDistanceCora (Z ∩ F) : ℝ) : WithBot ℝ)  -- 191. d
    else ⊥
  if dFo ≤ 0 then true else false                                 -- 280. (d_Go <= 0) && (d_Fo <= 0)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The verdict is `true` although `1 ∈ Z` lies in the unsafe set `x ≥ 1`. -/
theorem LinearSys.verifyRAOuterVerdictCora_touch_counterexample :
    LinearSys.verifyRAOuterVerdictCora (Set.Icc (-1) 1) (Set.Ici 1) = true ∧
      (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1 := by -- --- PROOF ---
  have hS : Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1 = {1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact le_antisymm h h'
    · rintro rfl; norm_num
  refine ⟨?_, by rw [hS]; rfl⟩
  have hne : (Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1).Nonempty := ⟨1, by rw [hS]; rfl⟩
  have hd : LinearSys.verifyRAIntersectionDistanceCora (Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1) = 0 := by
    rw [hS]; simp [LinearSys.verifyRAIntersectionDistanceCora]
  simp [LinearSys.verifyRAOuterVerdictCora, hne, hd]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
