module

public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.ContSet.Operations.SupportBoundSetLinComb

@[expose] public section

/-!
# `HPolytope.linCombOf`

CORA's `linComb`, on chosen directions: a point between the two polytopes is a weighted average
of one from each, so it beats neither bound and the larger of the two serves. A halfspace
description is convex, so here `linComb` and the convex hull agree; the distinction the
interface keeps is for representations that are not.

This is the template enclosure of the convex hull of two H-polytopes, [1, Eq. 31], with any
upper bounds in place of the support function values the paper takes.

## Inputs
* `Aq` – family indexed by `Fin q`
* `u₁` – a support bound of `P₁.construct` along each row
* `u₂` – a support bound of `P₂.construct` along each row

## Output
* the polytope on the directions `Aq` bounded by the larger of the bounds of `u₁` and `u₂`
## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {P₁ P₂ : HPolytope α}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.linCombOf (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => (u₁ i).setLinComb (u₂ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
