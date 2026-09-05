import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

/-!
# `PolyZonotope.mul` is exactly the product over shared factors

What exactness can mean here, and what it cannot: `construct (mul S₁ S₂)` is not
`construct S₁ * construct S₂`. Both sets are functions of one shared factor
vector, so their pointwise product ranges over far fewer points than the product
of the two sets. The claim is about the evaluation map — the result is exactly
the image of the admissible factors under `a ↦ point S₁ a ⊙ point S₂ a`, with
`S₂` read at the same factors through `Fin.cast`.

`sum_ext_eq_point` makes each point one sum, `Finset.sum_mul_sum` expands the
product over pairs, and adding the two exponent columns — sound only because the
factors are shared — turns each pair of monomials into one monomial.
`finProdFinEquiv` matches the pair index to the flat one the result carries.

The independent blocks are not hypothesised away: `point` ignores them, so they
take no part on either side.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}

/-- The result's monomial at a pair of columns: the two sets' monomials,
multiplied. -/
theorem PolyZonotope.aux_monomial_mulE (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) (l₁ : Fin (S₁.h + 1)) (l₂ : Fin (S₂.h + 1)) :
    monomial (mulE S₁ S₂ hp) a (finProdFinEquiv (l₁, l₂))
      = extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂ := by
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
theorem PolyZonotope.aux_mul_point (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l := by
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
    rw [Pi.smul_apply, smul_eq_mul, PolyZonotope.aux_monomial_mulE S₁ S₂ hp a l₁ l₂]
    refine congrArg _ ?_
    show PolyZonotope.extG S₁ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).1 i
        * PolyZonotope.extG S₂ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).2 i
      = extG S₁ l₁ i * extG S₂ l₂ i
    rw [Equiv.symm_apply_apply]
  rw [hL, hR]

theorem PolyZonotope.mul_exact (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    (fun a : Fin S₁.p → ℝ => S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (S₁.mul S₂ hp).construct := by
  -- the result has an empty independent block, so a point of it is the sum alone
  have hpt : ∀ (a : Fin S₁.p → ℝ) (b : Fin 0 → ℝ),
      S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
        = (0 : Vec ℝ n) + (∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ n) := by
    intro a b
    rw [PolyZonotope.aux_mul_point S₁ S₂ hp a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, fun _ => 0, ha, fun j => j.elim0, hpt a fun _ => 0⟩
  -- back, the same factor vector reused and the empty block read as it is
  · rintro x ⟨a, b, ha, _, hx⟩
    exact ⟨a, ha, by rw [hx]; exact hpt a b⟩

end CORALean.Real
