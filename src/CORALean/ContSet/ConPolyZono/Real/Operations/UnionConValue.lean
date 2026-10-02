import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionMeanSq
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnionWithSel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# What the selector constraint's row evaluates to

The eight column groups of [1, Thm. 1]'s selector row sum to the factored form
`(1 + α₁ + ½f₁(1-α₁))(1 - ½f₂) - α₂ - 1`, with `f₁`, `f₂` the two blocks' square
means. That form is the whole point of the row: on `α₁ = 1` it collapses to
`-f₂` and on `α₁ = -1` to `f₁(1 - ½f₂)`, so one row pins one block or the other.

The cross group is summed by transporting `Fin (p₁ p₂)` along `finProdFinEquiv`
and separating the two square sums, which is where the product `f₁f₂` comes from.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.unionCon_value {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ) :
    (∑ l, ConPolyZono.unionConCoef p₁ p₂ l * ∏ k, a k ^ ConPolyZono.unionConCol p₁ p₂ l k)
      = (1 + a (ConPolyZono.unionSel p₁ p₂)
            + 2⁻¹ * ConPolyZono.unionMeanSq (fun j => a (Fin.castAdd 2 (Fin.castAdd p₂ j)))
              * (1 - a (ConPolyZono.unionSel p₁ p₂)))
          * (1 - 2⁻¹ * ConPolyZono.unionMeanSq (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))))
        - a (Fin.natAdd (p₁ + p₂) 1) - 1 := by -- --- PROOF ---
  -- the cross group, at an arbitrary coefficient, as a product of two square sums
  have hcross : ∀ γ : ℝ,
      (∑ l : Fin (p₁ * p₂), γ * ∏ k, a k ^ ConPolyZono.unionCrossCol p₁ p₂ l k)
        = γ * ((∑ j, a (Fin.castAdd 2 (Fin.castAdd p₂ j)) ^ 2)
          * ∑ k, a (Fin.castAdd 2 (Fin.natAdd p₁ k)) ^ 2) := by
    intro γ
    have hterm : ∀ l : Fin (p₁ * p₂), (∏ k, a k ^ ConPolyZono.unionCrossCol p₁ p₂ l k)
        = a (Fin.castAdd 2 (Fin.castAdd p₂ (finProdFinEquiv.symm l).1)) ^ 2
          * a (Fin.castAdd 2 (Fin.natAdd p₁ (finProdFinEquiv.symm l).2)) ^ 2 := by
      intro l
      simp only [ConPolyZono.unionCrossCol]
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol]
    simp only [hterm]
    rw [← Equiv.sum_comp finProdFinEquiv (fun l : Fin (p₁ * p₂) =>
      γ * (a (Fin.castAdd 2 (Fin.castAdd p₂ (finProdFinEquiv.symm l).1)) ^ 2
        * a (Fin.castAdd 2 (Fin.natAdd p₁ (finProdFinEquiv.symm l).2)) ^ 2))]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  -- the eight groups, split apart along the column layout
  rw [Fin.sum_univ_add (a := 2) (b := p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))),
    Fin.sum_univ_add (a := p₁ + p₁) (b := p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)),
    Fin.sum_univ_add (a := p₁) (b := p₁),
    Fin.sum_univ_add (a := p₂ + p₂) (b := p₁ * p₂ + p₁ * p₂),
    Fin.sum_univ_add (a := p₂) (b := p₂),
    Fin.sum_univ_add (a := p₁ * p₂) (b := p₁ * p₂),
    Fin.sum_univ_two]
  simp only [ConPolyZono.unionConCol, ConPolyZono.unionConCoef, Fin.append_left,
    Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one, ConPolyZono.prod_unitCol,
    ConPolyZono.prod_unionWithSel, pow_one, ← mul_assoc]
  -- each group's coefficient pulled out of its sum, and the means read back
  rw [hcross, hcross, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp only [ConPolyZono.unionMeanSq]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
