module

public import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTerms
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `addedTerms` is the weighted sum

At the factor vector `(a, l)` the one-dimensional polynomial zonotope `addedTerms pZ` has the
point `∑ᵢ lᵢ · (pZ.point a)ᵢ`: each dimension's block is its centre and generators times the
monomial of `a`, and the new factor `lᵢ` enters with exponent `1` and no other.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The monomial of the block `(i, g)`: the original column's monomial times `lᵢ`. -/
theorem PolyZonotope.aux_monomial_addedTerms (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ)
    (l : Fin n → ℝ) (i : Fin n) (g : Fin (pZ.h + 1)) :
    PolyZonotope.monomial pZ.addedTerms.E (Fin.append a l) (finProdFinEquiv (i, g))
      = PolyZonotope.extM pZ a g * l i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  show ∏ k : Fin (pZ.p + n), (Fin.append a l : Fin (pZ.p + n) → ℝ) k ^
      (Fin.addCases (fun k' => pZ.extE k' (finProdFinEquiv.symm (finProdFinEquiv (i, g))).2)
        (fun j => if j = (finProdFinEquiv.symm (finProdFinEquiv (i, g))).1 then 1 else 0) k : ℕ)
      = _
  rw [Fin.prod_univ_add]
  simp only [Equiv.symm_apply_apply, Fin.append_left, Fin.append_right, Fin.addCases_left,
    Fin.addCases_right]
  congr 1
  simp [pow_ite]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.addedTerms_point (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ)
    (l : Fin n → ℝ) :
    pZ.addedTerms.point (Fin.append a l) = ∑ i, l i * pZ.point a i := by -- --- PROOF ---
  unfold PolyZonotope.point
  show (0 : ℝ) + ∑ idx : Fin (n * (pZ.h + 1)),
      PolyZonotope.monomial pZ.addedTerms.E (Fin.append a l) idx • pZ.addedTerms.G idx = _
  rw [zero_add]
  -- the flat generator index is the pair (dimension `i`, generator `g`)
  refine (Fintype.sum_equiv finProdFinEquiv
    (fun pr : Fin n × Fin (pZ.h + 1) => PolyZonotope.monomial pZ.addedTerms.E (Fin.append a l)
      (finProdFinEquiv pr) • pZ.addedTerms.G (finProdFinEquiv pr)) _ fun _ => rfl).symm.trans ?_
  refine (Fintype.sum_prod_type' (fun (i : Fin n) (g : Fin (pZ.h + 1)) =>
    PolyZonotope.monomial pZ.addedTerms.E (Fin.append a l) (finProdFinEquiv (i, g))
      • pZ.addedTerms.G (finProdFinEquiv (i, g)))).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  -- dimension `i`'s block is `lᵢ` times the `i`-th entry of the point
  have hpt : (∑ g, PolyZonotope.extM pZ a g • PolyZonotope.extG pZ g) i
      = (pZ.c + ∑ g, PolyZonotope.monomial pZ.E a g • pZ.G g) i :=
    congrFun (PolyZonotope.sum_ext_eq_point pZ a) i
  have hG : ∀ g, pZ.addedTerms.G (finProdFinEquiv (i, g)) = PolyZonotope.extG pZ g i := fun g => by
    simp [PolyZonotope.addedTerms, PolyZonotope.extG]
  simp only [PolyZonotope.aux_monomial_addedTerms, smul_eq_mul, hG]
  rw [← hpt, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
