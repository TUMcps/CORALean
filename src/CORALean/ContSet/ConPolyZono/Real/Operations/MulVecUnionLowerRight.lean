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

/-!
# A row of the second operand's block of the union's lower constraint

The mirror of `mulVec_unionLower_left` in [1, Thm. 1], the selector column
entering with the opposite sign so that this operand's constraint binds on the
branch where the first one's falls away.

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

theorem ConPolyZono.mulVec_unionLower_right {p₁ p₂ m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (b₁ : Interval (Vec ℝ m₁)) (A₂ : Mat ℝ m₂ s₂) (b₂ : Interval (Vec ℝ m₂))
    (EC₁ : Fin p₁ → Fin s₁ → ℕ) (EC₂ : Fin p₂ → Fin s₂ → ℕ)
    (a : Fin (p₁ + p₂ + 2) → ℝ) (i : Fin m₂) :
    (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        *ᵥ PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a) (Fin.natAdd m₁ i)
      = (A₂ *ᵥ PolyZonotope.monomial EC₂ fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))) i
        + 2⁻¹ * b₂.inf i * a (ConPolyZono.unionSel p₁ p₂) := by -- --- PROOF ---
  show (∑ l, ConPolyZono.unionLowerA A₁ b₁ A₂ b₂ (Fin.natAdd m₁ i) l
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
  -- and the block itself, which is `plusA`'s right half over its own monomials
  have hblk : (∑ l : Fin (s₁ + s₂), ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        (Fin.natAdd m₁ i) (Fin.castAdd 1 l)
        * PolyZonotope.monomial (ConPolyZono.unionLowerEC EC₁ EC₂) a (Fin.castAdd 1 l))
      = (A₂ *ᵥ PolyZonotope.monomial EC₂
          fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))) i := by
    simp only [ConPolyZono.unionLowerA, Fin.append_left, hmon]
    rw [show (∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.natAdd m₁ i) l
          * PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂)
            (fun k => a (Fin.castAdd 2 k)) l)
        = (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE EC₁ EC₂)
            fun k => a (Fin.castAdd 2 k)) (Fin.natAdd m₁ i) from rfl,
      ConPolyZono.mulVec_plusA_right]
    congr 1
    exact funext fun l => PolyZonotope.monomial_plusE_right EC₁ EC₂ _ l
  rw [hblk, hlast]
  simp only [ConPolyZono.unionLowerA, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
