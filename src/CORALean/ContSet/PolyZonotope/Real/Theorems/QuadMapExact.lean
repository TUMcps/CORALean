import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact

/-!
# `PolyZonotope.quadMap` is exactly the image under a quadratic map

The claim the representation exists for. Two facts carry it: a point is a single
sum once the centre is generator zero, and the product of two monomials is the
monomial of the added exponent columns — `monomial_add`, which holds only
because the factors are shared. Bilinearity then turns the map of a sum into a
double sum over pairs of generators, which is exactly what the result indexes.

The same coefficients work in both directions, so the image is reproduced and
not enclosed. `quadMapDep` needs an empty independent block, which its statement
asks for; `quadMap` supplies it by running `dependent` first, and `dependent` is
exact, so nothing is lost on the way in either.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n m : ℕ}

/-- A point of the set as one sum, the centre being generator zero at the
all-zero exponent column. -/
theorem PolyZonotope.aux_ext_point (S : PolyZonotope α) (a : Fin S.p → ℝ) :
    ∑ l, extM S a l • extG S l = S.c + ∑ i, monomial S.E a i • S.G i := by
  have h0 : extM S a 0 = 1 := by
    show ∏ k, a k ^ PolyZonotope.extE S k 0 = 1
    exact Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.extE, Fin.cons_zero, pow_zero]
  have hG0 : extG S 0 = S.c := by
    simp only [PolyZonotope.extG, Fin.cons_zero]
  have hsucc : ∀ i : Fin S.h,
      extM S a i.succ • extG S i.succ = monomial S.E a i • S.G i := by
    intro i
    have hm : extM S a i.succ = monomial S.E a i := by
      show ∏ k, a k ^ PolyZonotope.extE S k i.succ = ∏ k, a k ^ S.E k i
      exact Finset.prod_congr rfl fun k _ => by
        simp only [PolyZonotope.extE, Fin.cons_succ]
    have hg : extG S i.succ = S.G i := by
      simp only [PolyZonotope.extG, Fin.cons_succ]
    rw [hm, hg]
  rw [Fin.sum_univ_succ, h0, hG0, one_smul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => hsucc i)

/-- The map of a sum, expanded over pairs. Bilinearity on the left, and
`monomial_add` on the right, meet at the same double sum. -/
theorem PolyZonotope.aux_quad_expand (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n))
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

/-- Exact where every coefficient is dependent, which `quadMap` arranges. -/
theorem PolyZonotope.quadMapDep_exact (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n))
    (hq : S.q = 0) :
    quadEval Q '' S.construct = (quadMapDep Q S).construct := by
  have hb0 : ∀ b : Fin S.q → ℝ, ∑ j, b j • S.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hquad : ∀ a : Fin S.p → ℝ,
      quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i)
        = ∑ l, monomial (quadMapE S) a l • quadMapG Q S l := by
    intro a
    rw [← PolyZonotope.aux_ext_point S a]
    exact PolyZonotope.aux_quad_expand Q S a
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, b, ha, _, rfl⟩, rfl⟩
    refine ⟨a, fun _ => 0, ha, fun j => j.elim0, ?_⟩
    show quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, b j • S.GI j)
        = (0 : Vec ℝ m) + (∑ l, monomial (quadMapE S) a l • quadMapG Q S l)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ m)
    rw [hb0 b, add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, (0:ℝ) • S.GI j,
      ⟨a, fun _ => 0, ha, fun _ => by norm_num, rfl⟩, ?_⟩
    show quadEval Q (S.c + ∑ i, monomial S.E a i • S.G i + ∑ j, (0:ℝ) • S.GI j)
        = (0 : Vec ℝ m) + (∑ l, monomial (quadMapE S) a l • quadMapG Q S l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ m)
    rw [hb0 (fun _ => 0), add_zero, hquad a]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]

theorem PolyZonotope.quadMap_exact (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    quadEval Q '' PZ.construct = (PZ.quadMap Q).construct := by
  rw [PZ.dependent_exact]
  exact PolyZonotope.quadMapDep_exact Q PZ.dependent rfl

end CORALean.Real
