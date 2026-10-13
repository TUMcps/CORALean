import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerEC
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# A row of the first operand's block of the union's lower constraint

The operand's own row of [1, Thm. 1] against its own factors, less what the
shared selector column contributes — `0.5 b₁.inf α₁`. At `α₁ = 1` that shift is exactly what
`unionLowerB` subtracted, so the row is the operand's own constraint; at
`α₁ = -1` it is what makes a row whose left side has fallen to `0` satisfiable.

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

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mulVec_unionLower_left {p₁ p₂ m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (b₁ : Interval (Vec ℝ m₁)) (A₂ : Mat ℝ m₂ s₂) (b₂ : Interval (Vec ℝ m₂))
    (EC₁ : Fin p₁ → Fin s₁ → ℕ) (EC₂ : Fin p₂ → Fin s₂ → ℕ)
    (a : Fin (p₁ + p₂ + 2) → ℝ) (i : Fin m₁) :
    (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        *ᵥ PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a) (Fin.castAdd m₂ i)
      = (A₁ *ᵥ PolyZonotope.monomial EC₁ fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i
        - 2⁻¹ * b₁.inf i * a (ConPolyZono.unionSel p₁ p₂) := by -- --- PROOF ---
  show (∑ l, ConPolyZono.unionLowerA A₁ b₁ A₂ b₂ (Fin.castAdd m₂ i) l
      * PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a l) = _
  rw [Fin.sum_univ_add (a := s₁ + s₂) (b := 1), Fin.sum_univ_one]
  -- the operands' own columns, read back against their own factors
  have hmon : ∀ l : Fin (s₁ + s₂),
      PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a (Fin.castAdd 1 l)
        = PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂)
          (fun k => a (Fin.castAdd 2 k)) l := fun l => by
    rw [ConPolyZono.unionLowerEC, ConPolyZono.monomial_appendE_left,
      ConPolyZono.monomial_padE]
  have hlast : PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a
      (Fin.natAdd (s₁ + s₂) 0) = a (ConPolyZono.unionSel p₁ p₂) := by
    rw [ConPolyZono.unionLowerEC, ConPolyZono.monomial_appendE_right,
      PolyZonotope.monomial, ConPolyZono.prod_unitCol, pow_one]
  -- and the block itself, which is `plusA`'s left half over its own monomials
  have hblk : (∑ l : Fin (s₁ + s₂), ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        (Fin.castAdd m₂ i) (Fin.castAdd 1 l)
        * PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a (Fin.castAdd 1 l))
      = (A₁ *ᵥ PolyZonotope.monomial EC₁
          fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i := by
    simp only [ConPolyZono.unionLowerA, Fin.append_left, hmon]
    rw [show (∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.castAdd m₂ i) l
          * PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂)
            (fun k => a (Fin.castAdd 2 k)) l)
        = (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂)
            fun k => a (Fin.castAdd 2 k)) (Fin.castAdd m₂ i) from rfl,
      ConPolyZono.mulVec_plusA_left]
    congr 1
    exact funext fun l => PolyZonotope.monomial_plusE_left EC₁ EC₂ _ l
  rw [hblk, hlast]
  simp only [ConPolyZono.unionLowerA, Fin.append_right, Fin.append_left]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
