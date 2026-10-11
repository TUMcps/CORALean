import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.EReal.Basic

/-!
# What the scan of [1, Alg. 3] does at one edge

Lines 11-15 (and 19-23): if the edge `[P; Q]` intersects `L_γ`, take the point `(x, y)` of
the intersection and update `m ← min(m, y)`, `M ← max(M, y)`. The intersection is a point unless
the edge is vertical and lies on `L_γ`, where the printed "`(x, y) ← [P; Q] ∩ L_γ`" names no
single `y`; the update is then read at every point of it, the least `y` for `m` and the greatest
for `M`. `m` and `M` start at `∞` and `-∞` (line 2), hence `EReal`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 3] lines 11-15: update `(m, M)` with the intersection of `[P; Q]` and `L_γ`. -/
noncomputable def Zonotope.scanEdge (γ : ℝ) (P Q : Vec ℝ 2) (mM : EReal × EReal) :
    EReal × EReal :=
  if (segment ℝ P Q ∩ {z | z 0 = γ}).Nonempty then              -- line 11
    let ym := sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q}  -- line 12: `(x, y) ← …`
    let yM := sSup {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q}
    (min mM.1 ym, max mM.2 yM)                                    -- lines 13-14
  else mM

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
