import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
import CORALean.HybridDynamics.Theorems.JumpIntersectionOfPointOuter

/-!
# The guard cut and the jump, chained

`ConPolyZonoGuard.lean` stops at the exact cut: `cPZ.intersection G.conPolyZono` really is
`cPZ.construct ∩ G.construct`, whether or not `cPZ` is convex. `jumpIntersectionOfPoint`
takes that cut set the rest of the way, the reset propagated over it, asking
only `OfPoint` — which `ConPolyZono` now has — where `jump`/`jumpIntersection` would
have asked for the `OfInterval` instance it still lacks (#38).

A concrete transition shifts the state by `(2, 2)`; a point sitting in both `cPZ`
and `G` is carried, by `jumpIntersectionOfPoint_outer`, to the concrete point `(3, 3)`
in the jumped set.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Leaves the state unscaled and shifts it by `(2, 2)`, at whatever guard a
caller names. -/
def GCR.trans (guard : ConPolyZono (Vec ℝ 2)) : Transition 𝒞𝒫𝒵 Unit ℝ 2 :=
  ⟨guard, (1 : Mat ℝ 2 2), ![2, 2], ()⟩

/-- `(1, 1)`, cut exactly by the guard through `conPolyZono_exact`, resets to
the concrete point `(3, 3)` — no `OfInterval` instance needed to place it. -/
example (cPZ : ConPolyZono (Vec ℝ 2)) (G : ConZonotope (Vec ℝ 2))
    (hz : (![1, 1] : Vec ℝ 2) ∈ cPZ.construct) (hguard : (![1, 1] : Vec ℝ 2) ∈ G.construct) :
    (![3, 3] : Vec ℝ 2) ∈
      construct ((GCR.trans G.conPolyZono).jumpIntersectionOfPoint cPZ) := by
  have hguard' : (![1, 1] : Vec ℝ 2) ∈ G.conPolyZono.construct := by
    rw [← ConZonotope.conPolyZono_exact G]; exact hguard
  have hreset : (GCR.trans G.conPolyZono).reset ![1, 1] = ![3, 3] := by
    funext i
    fin_cases i <;> norm_num [Transition.reset, GCR.trans, Matrix.one_mulVec]
  rw [← hreset]
  exact (GCR.trans G.conPolyZono).jumpIntersectionOfPoint_outer hz hguard'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
