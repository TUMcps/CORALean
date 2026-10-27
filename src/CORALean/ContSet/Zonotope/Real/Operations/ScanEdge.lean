module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# What the scan of [1, Alg. 3] does at one edge

Lines 11-15 (and 19-23): if the edge `[P; Q]` intersects `L_γ`, take the point `(x, y)` of
the intersection and update `m ← min(m, y)`, `M ← max(M, y)`. The intersection is a point unless
the edge is vertical and lies on `L_γ`, where the printed "`(x, y) ← [P; Q] ∩ L_γ`" names no
single `y`; the update is then read at every point of it, the least `y` for `m` and the greatest
for `M`. `m` and `M` start at `∞` and `-∞` (line 2), hence `EReal`.

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 3] lines 11-15: update `(m, M)` with the intersection of `[P; Q]` and `L_γ`. -/
noncomputable def Zonotope.scanEdge (γ : ℝ) (P Q : Vec ℝ 2) (mM : Interval EReal) :
    Interval EReal :=
  -- 11. if `[P; Q]` intersects `L_γ`
  if (segment ℝ P Q ∩ {z | z 0 = γ}).Nonempty then
    -- 12. `(x, y) ← [P; Q] ∩ L_γ`, read at every point of it: the least `y` and the greatest
    let ym := sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q}
    let yM := sSup {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q}
    -- 13. `m ← min(m, y)`, and line 14, `M ← max(M, y)`
    ⟨min mM.inf ym, max mM.sup yM⟩
  else mM

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
