module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionG
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# The union's generator sum, split into its three pieces

The selector's own generator and the two operands' blocks of [1, Thm. 1], each
read back against the factors it came with. Every step is a monomial lemma:
`appendE` separates the selector column, `padE` drops the fresh factors, `plusE`
separates the two operands.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.sum_unionE {p₁ h₁ p₂ h₂ : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]
    (c₁ c₂ : α) (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α) (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial (ConPolyZono.unionE E₁ E₂) a i
        • ConPolyZono.unionG c₁ c₂ G₁ G₂ i)
      = a (ConPolyZono.unionSel p₁ p₂) • ((2 : ℝ)⁻¹ • (c₁ - c₂))
        + ((∑ i, PolyZonotope.monomial E₁ (fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i
              • G₁ i)
          + ∑ i, PolyZonotope.monomial E₂ (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))) i
              • G₂ i) := by -- --- PROOF ---
  rw [Fin.sum_univ_add (a := 1) (b := h₁ + h₂), Fin.sum_univ_one]
  congr 1
  · -- the selector's generator, its monomial the selector itself
    rw [ConPolyZono.unionE, ConPolyZono.monomial_appendE_left, PolyZonotope.monomial,
      ConPolyZono.prod_unitCol, pow_one, ConPolyZono.unionG, Fin.append_left]
  · rw [Fin.sum_univ_add (a := h₁) (b := h₂)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ConPolyZono.unionE, ConPolyZono.monomial_appendE_right, ConPolyZono.monomial_padE,
        PolyZonotope.monomial_plusE_left, ConPolyZono.unionG, Fin.append_right,
        Fin.append_left]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ConPolyZono.unionE, ConPolyZono.monomial_appendE_right, ConPolyZono.monomial_padE,
        PolyZonotope.monomial_plusE_right, ConPolyZono.unionG, Fin.append_right,
        Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
