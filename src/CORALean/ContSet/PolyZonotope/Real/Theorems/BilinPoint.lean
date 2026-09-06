import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

/-!
# `bilin`'s point is `f` at the two points

The whole content of the construction, and the only place bilinearity is used:
`sum_ext_eq_point` makes each point one sum, `f` distributes over both, and
adding the two exponent columns — sound only because the factors are shared —
turns each pair of monomials into one, at the flat index `finProdFinEquiv`
matches to the pair.

Stated over `point` rather than over `construct`, because the recursion that
raises a polynomial abstraction one order needs it at each step and only
`bilin_exact` needs it over the sets.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α β γ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The result's monomial at a pair of columns: the two sets' monomials,
multiplied. -/
theorem PolyZonotope.aux_bilin_monomial (S₁ : PolyZonotope α) (S₂ : PolyZonotope β)
    (hp : S₁.p = S₂.p) (a : Fin S₁.p → ℝ) (l₁ : Fin (S₁.h + 1)) (l₂ : Fin (S₂.h + 1)) :
    monomial (bilinE S₁ S₂ hp) a (finProdFinEquiv (l₁, l₂))
      = extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂ := by -- --- PROOF ---
  -- `S₂`'s factor index is `S₁`'s renamed, so the two products run over one set
  have hcast : ∏ k : Fin S₁.p, a k ^ PolyZonotope.extE S₂ (Fin.cast hp k) l₂
      = ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂ :=
    Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl
  show ∏ k, a k ^ PolyZonotope.bilinE S₁ S₂ hp k (finProdFinEquiv (l₁, l₂))
      = (∏ k, a k ^ PolyZonotope.extE S₁ k l₁)
        * ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂
  rw [← hcast, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [PolyZonotope.bilinE, Equiv.symm_apply_apply]
  exact pow_add (a k) _ _

variable [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]

/-- `f` at the two points, expanded over pairs of extended columns — the step
that uses bilinearity and nothing else. -/
theorem PolyZonotope.aux_bilin_pair (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (S₁ : PolyZonotope α)
    (S₂ : PolyZonotope β) (hp : S₁.p = S₂.p) (a : Fin S₁.p → ℝ) :
    f (S₁.point a) (S₂.point fun k => a (Fin.cast hp.symm k))
      = ∑ l₁, ∑ l₂, (extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          • f (extG S₁ l₁) (extG S₂ l₂) := by -- --- PROOF ---
  have h₁ : S₁.point a = ∑ l, extM S₁ a l • extG S₁ l :=
    (PolyZonotope.sum_ext_eq_point S₁ a).symm
  have h₂ : S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, extM S₂ (fun k => a (Fin.cast hp.symm k)) l • extG S₂ l :=
    (PolyZonotope.sum_ext_eq_point S₂ _).symm
  -- linear in the first argument, then in the second, and the two scalars merge
  have hout : f (∑ l, extM S₁ a l • extG S₁ l) = ∑ l, f (extM S₁ a l • extG S₁ l) :=
    map_sum f _ Finset.univ
  rw [h₁, h₂, hout, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l₁ _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l₂ _ => by rw [map_smul, smul_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `bilin`'s point, read off the expansion above rather than `construct`: `f`
at the two points, `S₂` read at `S₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.bilin_point (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (S₁ : PolyZonotope α)
    (S₂ : PolyZonotope β) (hp : S₁.p = S₂.p) (a : Fin S₁.p → ℝ) :
    (S₁.bilin f S₂ hp).point a
      = f (S₁.point a) (S₂.point fun k => a (Fin.cast hp.symm k)) := by -- --- PROOF ---
  -- the pairs and the flat generator index are the same sum, reindexed
  have hpair : ∑ pr : Fin (S₁.h + 1) × Fin (S₂.h + 1),
        monomial (bilinE S₁ S₂ hp) a (finProdFinEquiv pr) • bilinG f S₁ S₂ (finProdFinEquiv pr)
      = ∑ l, monomial (bilinE S₁ S₂ hp) a l • bilinG f S₁ S₂ l :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  show (0 : γ) + ∑ l, monomial (bilinE S₁ S₂ hp) a l • bilinG f S₁ S₂ l = _
  rw [zero_add, ← hpair, Fintype.sum_prod_type, PolyZonotope.aux_bilin_pair f S₁ S₂ hp a]
  refine Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => ?_
  rw [PolyZonotope.aux_bilin_monomial S₁ S₂ hp a l₁ l₂]
  refine congrArg _ ?_
  show f (extG S₁ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).1)
      (extG S₂ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).2)
    = f (extG S₁ l₁) (extG S₂ l₂)
  rw [Equiv.symm_apply_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
