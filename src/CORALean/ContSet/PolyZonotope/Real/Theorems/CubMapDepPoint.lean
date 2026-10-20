module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep
public import CORALean.ContSet.PolyZonotope.Real.Operations.CubEvalMixed
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

@[expose] public section

/-!
# The point of `cubMapDepOn`

The cubic map as a polynomial in the very factors `P` is written in, rather than as an enclosure
of it: at every factor vector `a` the point of the result is the cubic map of the point of `P`
at `a`, `zᵢ = Σₖ (π₃ x)ₖ ((π₁ x)ᵀ T{i,k} (π₂ x))` with `x = P.point a`. Two applications of
`bilin_point`, the quadratic forms first.

## Inputs
* `π₁` – first projection to vectors
* `π₂` – second projection to vectors
* `π₃` – third projection to vectors
* `T` – family of cubic form tensors
* `P` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the point is the mixed cubic map of the projected points
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMapDepOn_point (π₁ π₂ π₃ : V →ₗ[ℝ] Vec ℝ n)
    (T : Fin m → Fin n → Mat ℝ n n) (P : PolyZonotope V) (a : Fin P.p → ℝ) : -- --- CONCL ---
    (cubMapDepOn π₁ π₂ π₃ T P).point a
      = cubEvalMixed T (π₁ (P.point a)) (π₂ (P.point a)) (π₃ (P.point a)) := by -- --- PROOF ---
  unfold cubMapDepOn
  rw [PolyZonotope.bilin_point]
  funext i
  simp only [Fin.cast_eq_self, LinearMap.compl₁₂_apply, PolyZonotope.bilin_point]
  show ∑ k, π₃ (P.point a) k * (PolyZonotope.quadBilin (PolyZonotope.aux_cubQuad T)
      (π₁ (P.point a)) (π₂ (P.point a))) (finProdFinEquiv (i, k)) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  show π₃ (P.point a) k * (π₁ (P.point a) ⬝ᵥ
      (PolyZonotope.aux_cubQuad T (finProdFinEquiv (i, k)) *ᵥ π₂ (P.point a))) = _
  simp only [PolyZonotope.aux_cubQuad, Equiv.symm_apply_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
