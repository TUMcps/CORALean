module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

@[expose] public section

/-!
# `bilin`'s point is `f` at the two points

The whole content of the construction, and the only place bilinearity is used:
`sum_ext_eq_point` makes each point one sum, `f` distributes over both, and adding the two
exponent columns (sound only because the factors are shared) turns each pair of monomials into
one, at the flat index `finProdFinEquiv` matches to the pair. Stated over `point` rather than
`construct`, since the recursion that raises the order needs it at each step.

## Inputs
* `f` – bilinear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the bilinear map of the two points
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α β γ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The result's monomial at a pair of columns: the two sets' monomials,
multiplied. -/
theorem PolyZonotope.aux_bilin_monomial (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (l₁ : Fin (pZ₁.h + 1)) (l₂ : Fin (pZ₂.h + 1)) :
    monomial (bilinE pZ₁ pZ₂ hp) a (finProdFinEquiv (l₁, l₂))
      = extM pZ₁ a l₁ * extM pZ₂ (fun k => a (Fin.cast hp.symm k)) l₂ := by -- --- PROOF ---
  -- `pZ₂`'s factor index is `pZ₁`'s renamed, so the two products run over one set
  have hcast : ∏ k : Fin pZ₁.p, a k ^ PolyZonotope.extE pZ₂ (Fin.cast hp k) l₂
      = ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE pZ₂ k l₂ :=
    Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl
  show ∏ k, a k ^ PolyZonotope.bilinE pZ₁ pZ₂ hp k (finProdFinEquiv (l₁, l₂))
      = (∏ k, a k ^ PolyZonotope.extE pZ₁ k l₁)
        * ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE pZ₂ k l₂
  rw [← hcast, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [PolyZonotope.bilinE, Equiv.symm_apply_apply]
  exact pow_add (a k) _ _

variable [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]

/-- `f` at the two points, expanded over pairs of extended columns — the step
that uses bilinearity and nothing else. -/
theorem PolyZonotope.aux_bilin_pair (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) : -- --- CONCL ---
    f (pZ₁.point a) (pZ₂.point fun k => a (Fin.cast hp.symm k))
      = ∑ l₁, ∑ l₂, (extM pZ₁ a l₁ * extM pZ₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          • f (extG pZ₁ l₁) (extG pZ₂ l₂) := by -- --- PROOF ---
  have h₁ : pZ₁.point a = ∑ l, extM pZ₁ a l • extG pZ₁ l :=
    (PolyZonotope.sum_ext_eq_point pZ₁ a).symm
  have h₂ : pZ₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, extM pZ₂ (fun k => a (Fin.cast hp.symm k)) l • extG pZ₂ l :=
    (PolyZonotope.sum_ext_eq_point pZ₂ _).symm
  -- linear in the first argument, then in the second, and the two scalars merge
  have hout : f (∑ l, extM pZ₁ a l • extG pZ₁ l) = ∑ l, f (extM pZ₁ a l • extG pZ₁ l) :=
    map_sum f _ Finset.univ
  rw [h₁, h₂, hout, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l₁ _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l₂ _ => by rw [map_smul, smul_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `bilin`'s point, read off the expansion above rather than `construct`: `f`
at the two points, `pZ₂` read at `pZ₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.bilin_point (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) :
    (pZ₁.bilin f pZ₂ hp).point a
      = f (pZ₁.point a) (pZ₂.point fun k => a (Fin.cast hp.symm k)) := by -- --- PROOF ---
  -- the pairs and the flat generator index are the same sum, reindexed
  have hpair : ∑ pr : Fin (pZ₁.h + 1) × Fin (pZ₂.h + 1),
        monomial (bilinE pZ₁ pZ₂ hp) a (finProdFinEquiv pr) • bilinG f pZ₁ pZ₂ (finProdFinEquiv pr)
      = ∑ l, monomial (bilinE pZ₁ pZ₂ hp) a l • bilinG f pZ₁ pZ₂ l :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  show (0 : γ) + ∑ l, monomial (bilinE pZ₁ pZ₂ hp) a l • bilinG f pZ₁ pZ₂ l = _
  rw [zero_add, ← hpair, Fintype.sum_prod_type, PolyZonotope.aux_bilin_pair f pZ₁ pZ₂ hp a]
  refine Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => ?_
  rw [PolyZonotope.aux_bilin_monomial pZ₁ pZ₂ hp a l₁ l₂]
  refine congrArg _ ?_
  show f (extG pZ₁ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).1)
      (extG pZ₂ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).2)
    = f (extG pZ₁ l₁) (extG pZ₂ l₂)
  rw [Equiv.symm_apply_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
