import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# A quadratic map of the extended sum, expanded over pairs

Bilinearity turns the map of a sum into a double sum over pairs of generators;
`monomial_add` — which holds only because the factors are shared — turns the
product of two monomials into the monomial of the added exponent columns. The
two meet at the same double sum, and `finProdFinEquiv` matches the pair index to
the flat one the result carries.

Pointwise in the factor vector, and public for that reason: the constrained
representation needs it at a fixed `a`, which a set equality cannot give.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}

/-- The map of a sum, expanded over pairs. Bilinearity on the left, and
`monomial_add` on the right, meet at the same double sum. -/
theorem PolyZonotope.quadEval_sum_ext (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n))
    (a : Fin S.p → ℝ) :
    quadEval Q (∑ l, extM S a l • extG S l)
      = ∑ l, monomial (quadMapE S) a l • quadMapG Q S l := by
  funext k
  have hmulsum : Q k *ᵥ (∑ l, extM S a l • extG S l)
      = ∑ l, Q k *ᵥ (extM S a l • extG S l) :=
    map_sum (Matrix.mulVecLin (Q k)) _ Finset.univ
  have hterm : ∀ l l' : Fin (S.h + 1),
      (extM S a l • extG S l) ⬝ᵥ (Q k *ᵥ (extM S a l' • extG S l'))
        = extM S a l * extM S a l' * (extG S l ⬝ᵥ (Q k *ᵥ extG S l')) := by
    intro l l'
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc]
  -- the left side as a double sum over pairs of extended columns
  have hL : quadEval Q (∑ l, extM S a l • extG S l) k
      = ∑ l, ∑ l', extM S a l * extM S a l' * (extG S l ⬝ᵥ (Q k *ᵥ extG S l')) := by
    show (∑ l, extM S a l • extG S l) ⬝ᵥ (Q k *ᵥ ∑ l, extM S a l • extG S l) = _
    rw [hmulsum, sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun l' _ => hterm l l'
  have hmono : ∀ p : Fin (S.h + 1) × Fin (S.h + 1),
      monomial (quadMapE S) a (finProdFinEquiv p) = extM S a p.1 * extM S a p.2 := by
    intro p
    show (∏ k', a k' ^ PolyZonotope.quadMapE S k' (finProdFinEquiv p))
        = (∏ k', a k' ^ PolyZonotope.extE S k' p.1)
          * ∏ k', a k' ^ PolyZonotope.extE S k' p.2
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k' _ => ?_
    simp only [PolyZonotope.quadMapE, Equiv.symm_apply_apply]
    exact pow_add (a k') _ _
  -- and the right side, `finProdFinEquiv` matching the pair index to the flat one
  have hpair : ∑ p : Fin (S.h + 1) × Fin (S.h + 1),
        (monomial (quadMapE S) a (finProdFinEquiv p) • quadMapG Q S (finProdFinEquiv p)) k
      = ∑ l, (monomial (quadMapE S) a l • quadMapG Q S l) k :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  have hR : (∑ l, monomial (quadMapE S) a l • quadMapG Q S l) k
      = ∑ l, ∑ l', extM S a l * extM S a l' * (extG S l ⬝ᵥ (Q k *ᵥ extG S l')) := by
    rw [Finset.sum_apply, ← hpair, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hmono]
    refine congrArg _ ?_
    show PolyZonotope.extG S (finProdFinEquiv.symm (finProdFinEquiv (l, l'))).1
        ⬝ᵥ (Q k *ᵥ PolyZonotope.extG S (finProdFinEquiv.symm (finProdFinEquiv (l, l'))).2)
      = extG S l ⬝ᵥ (Q k *ᵥ extG S l')
    rw [Equiv.symm_apply_apply]
  rw [hL, hR]

end CORALean.Real
