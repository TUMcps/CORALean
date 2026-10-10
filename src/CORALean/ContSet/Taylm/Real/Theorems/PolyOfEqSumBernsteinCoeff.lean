import CORALean.ContSet.Taylm.Real.Operations.BernsteinCoeff
import CORALean.ContSet.Taylm.Real.Theorems.PowEqSumBernsteinEntry

/-!
# A polynomial as its Bernstein expansion

With every exponent at most `N`, the polynomial of a term list is the Bernstein expansion with
the coefficients `bernsteinCoeff` [1]: `Σ_β b_β ∏ₖ B_{βₖ,N}((tₖ + 1)/2)`. Term by term (induction
on the list), a monomial is the product over variables of its one-variable expansion
(`pow_eq_sum_bernsteinEntry`), and a product of sums is the sum over multi-indices.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_eq_sum_bernsteinCoeff (L : List (ℝ × (Fin n → ℕ))) (N : ℕ)
    (hL : ∀ a ∈ L, ∀ k, a.2 k ≤ N) (t : Vec ℝ n) :
    Taylm.polyOf L t = ∑ β : Fin n → Fin (N + 1), Taylm.bernsteinCoeff L N β *
      ∏ k, Taylm.bernsteinBasis N (β k) ((t k + 1) / 2) := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.bernsteinCoeff]
  | cons a L ih =>
    have hL' : ∀ b ∈ L, ∀ k, b.2 k ≤ N := fun b hb => hL b (List.mem_cons_of_mem a hb)
    -- the head term, a monomial, as a sum over multi-indices
    have hmono : Taylm.monomial a.2 t = ∑ β : Fin n → Fin (N + 1),
        (∏ k, Taylm.bernsteinEntry N (a.2 k) (β k)) *
          ∏ k, Taylm.bernsteinBasis N (β k) ((t k + 1) / 2) := by
      unfold Taylm.monomial
      have h1 : ∀ k, t k ^ a.2 k = ∑ j : Fin (N + 1), Taylm.bernsteinEntry N (a.2 k) j *
          Taylm.bernsteinBasis N j ((t k + 1) / 2) := fun k => by
        rw [Taylm.pow_eq_sum_bernsteinEntry N (a.2 k) (hL a (List.mem_cons_self) k) (t k),
          Finset.sum_range]
      simp_rw [h1]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.prod_mul_distrib]
    -- the head term's share of the coefficients, then the rest by induction
    rw [Taylm.polyOf_cons, ih hL', hmono, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold Taylm.bernsteinCoeff
    simp only [List.map_cons, List.sum_cons]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
