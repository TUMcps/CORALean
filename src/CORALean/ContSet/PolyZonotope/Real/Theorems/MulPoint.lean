import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

/-!
# `mul`'s point is the product of the two points

Shared by `MulExact` and `EvalPolyExact`, which both need it and cannot import
one another: `mul_exact` states it over the sets, `evalPoly_exact`'s recursion
over the sets' points at each Horner step. `sum_ext_eq_point` makes each point
one sum, `Finset.sum_mul_sum` expands the product over pairs, and adding the two
exponent columns — sound only because the factors are shared — turns each pair
of monomials into one, at the flat index `finProdFinEquiv` matches to the pair.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The result's monomial at a pair of columns: the two sets' monomials,
multiplied. -/
theorem PolyZonotope.aux_mul_monomial (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) (l₁ : Fin (S₁.h + 1)) (l₂ : Fin (S₂.h + 1)) :
    monomial (mulE S₁ S₂ hp) a (finProdFinEquiv (l₁, l₂))
      = extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂ := by -- --- PROOF ---
  -- `S₂`'s factor index is `S₁`'s renamed, so the two products run over one set
  have hcast : ∏ k : Fin S₁.p, a k ^ PolyZonotope.extE S₂ (Fin.cast hp k) l₂
      = ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂ :=
    Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl
  show ∏ k, a k ^ PolyZonotope.mulE S₁ S₂ hp k (finProdFinEquiv (l₁, l₂))
      = (∏ k, a k ^ PolyZonotope.extE S₁ k l₁)
        * ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂
  rw [← hcast, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [PolyZonotope.mulE, Equiv.symm_apply_apply]
  exact pow_add (a k) _ _

/-- The product of the two points, expanded over pairs of extended columns. -/
theorem PolyZonotope.aux_mul_point_sum (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l := by -- --- PROOF ---
  funext i
  have h₁ : S₁.point a = ∑ l, extM S₁ a l • extG S₁ l :=
    (PolyZonotope.sum_ext_eq_point S₁ a).symm
  have h₂ : S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, extM S₂ (fun k => a (Fin.cast hp.symm k)) l • extG S₂ l :=
    (PolyZonotope.sum_ext_eq_point S₂ _).symm
  -- the left side as a double sum over pairs of extended columns
  have hL : (S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))) i
      = ∑ l₁, ∑ l₂, (extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          * (extG S₁ l₁ i * extG S₂ l₂ i) := by
    show (S₁.point a) i * (S₂.point (fun k => a (Fin.cast hp.symm k))) i = _
    rw [h₁, h₂, Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => by ring
  have hpair : ∑ pr : Fin (S₁.h + 1) × Fin (S₂.h + 1),
        (monomial (mulE S₁ S₂ hp) a (finProdFinEquiv pr) • mulG S₁ S₂ (finProdFinEquiv pr)) i
      = ∑ l, (monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l) i :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  -- and the right side, `finProdFinEquiv` matching the pair index to the flat one
  have hR : (∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l) i
      = ∑ l₁, ∑ l₂, (extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          * (extG S₁ l₁ i * extG S₂ l₂ i) := by
    rw [Finset.sum_apply, ← hpair, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, PolyZonotope.aux_mul_monomial S₁ S₂ hp a l₁ l₂]
    refine congrArg _ ?_
    show PolyZonotope.extG S₁ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).1 i
        * PolyZonotope.extG S₂ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).2 i
      = extG S₁ l₁ i * extG S₂ l₂ i
    rw [Equiv.symm_apply_apply]
  rw [hL, hR]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mul`'s point, read off the expansion above rather than `construct`: a
product of the two points, `S₂` read at `S₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.mul_point (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    (S₁.mul S₂ hp).point a = S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)) := by
  show (0 : Vec ℝ n) + ∑ l, PolyZonotope.monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l
      = S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
  rw [zero_add, PolyZonotope.aux_mul_point_sum S₁ S₂ hp a]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
