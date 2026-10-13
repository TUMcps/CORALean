module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# `SPLIT_PIVOT`: the generators below the pivot and the rest

Line 16 of [1, Alg. 4]: the generators of `G` "smaller" and "bigger", "according to the
trigonometric order", than the pivot vector `s`. Smaller means a smaller angle `Complex.arg` when
the search goes right (`right`), and a larger one when it goes left, the order in which the walk
from the lowest vertex meets the generators on that side. The paper does not say so for the left
side, where the printed order would take the walk's far end first and so find the other boundary.

The pivot `s` is the sum of the generators of `G`, so its angle is strictly between the extremes
unless all of `G` is parallel, where nothing is smaller than the pivot and the split must still
divide `G`: it then takes off the generator of least index.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 4] line 16: `(G<, G>)` of `G` at the pivot `s`. -/
noncomputable def Zonotope.splitPivot (Z : Zonotope (Vec ℝ 2)) (right : Bool)
    (G : Finset (Fin Z.h)) (s : Vec ℝ 2) : Finset (Fin Z.h) × Finset (Fin Z.h) :=
  let G₁ := G.filter fun i => if right then Complex.arg ⟨Z.G i 0, Z.G i 1⟩ < Complex.arg ⟨s 0, s 1⟩
    else Complex.arg ⟨s 0, s 1⟩ < Complex.arg ⟨Z.G i 0, Z.G i 1⟩
  if G₁.Nonempty then (G₁, G \ G₁)
  else (G.filter fun i => ∀ j ∈ G, i ≤ j, G.filter fun i => ¬ ∀ j ∈ G, i ≤ j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
