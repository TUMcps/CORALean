module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerR
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

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

theorem ConPolyZono.mulVec_unionLower_left {p₁ p₂ m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (b₁ : Interval (Vec ℝ m₁)) (A₂ : Mat ℝ m₂ q₂) (b₂ : Interval (Vec ℝ m₂))
    (R₁ : Fin p₁ → Fin q₁ → ℕ) (R₂ : Fin p₂ → Fin q₂ → ℕ)
    (a : Fin (p₁ + p₂ + 2) → ℝ) (i : Fin m₁) :
    (ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        *ᵥ PolyZonotope.monomial (ConPolyZono.unionLowerR R₁ R₂) a) (Fin.castAdd m₂ i)
      = (A₁ *ᵥ PolyZonotope.monomial R₁ fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i
        - 2⁻¹ * b₁.inf i * a (ConPolyZono.unionSel p₁ p₂) := by -- --- PROOF ---
  show (∑ l, ConPolyZono.unionLowerA A₁ b₁ A₂ b₂ (Fin.castAdd m₂ i) l
      * PolyZonotope.monomial (ConPolyZono.unionLowerR R₁ R₂) a l) = _
  rw [Fin.sum_univ_add (a := q₁ + q₂) (b := 1), Fin.sum_univ_one]
  -- the operands' own columns, read back against their own factors
  have hmon : ∀ l : Fin (q₁ + q₂),
      PolyZonotope.monomial (ConPolyZono.unionLowerR R₁ R₂) a (Fin.castAdd 1 l)
        = PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂)
          (fun k => a (Fin.castAdd 2 k)) l := fun l => by
    rw [ConPolyZono.unionLowerR, ConPolyZono.monomial_appendE_left,
      ConPolyZono.monomial_padE]
  have hlast : PolyZonotope.monomial (ConPolyZono.unionLowerR R₁ R₂) a
      (Fin.natAdd (q₁ + q₂) 0) = a (ConPolyZono.unionSel p₁ p₂) := by
    rw [ConPolyZono.unionLowerR, ConPolyZono.monomial_appendE_right,
      PolyZonotope.monomial, ConPolyZono.prod_unitCol, pow_one]
  -- and the block itself, which is `plusA`'s left half over its own monomials
  have hblk : (∑ l : Fin (q₁ + q₂), ConPolyZono.unionLowerA A₁ b₁ A₂ b₂
        (Fin.castAdd m₂ i) (Fin.castAdd 1 l)
        * PolyZonotope.monomial (ConPolyZono.unionLowerR R₁ R₂) a (Fin.castAdd 1 l))
      = (A₁ *ᵥ PolyZonotope.monomial R₁
          fun k => a (Fin.castAdd 2 (Fin.castAdd p₂ k))) i := by
    simp only [ConPolyZono.unionLowerA, Fin.append_left, hmon]
    rw [show (∑ l : Fin (q₁ + q₂), ConPolyZono.plusA A₁ A₂ (Fin.castAdd m₂ i) l
          * PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂)
            (fun k => a (Fin.castAdd 2 k)) l)
        = (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂)
            fun k => a (Fin.castAdd 2 k)) (Fin.castAdd m₂ i) from rfl,
      ConPolyZono.mulVec_plusA_left]
    congr 1
    exact funext fun l => PolyZonotope.monomial_plusE_left R₁ R₂ _ l
  rw [hblk, hlast]
  simp only [ConPolyZono.unionLowerA, Fin.append_right, Fin.append_left]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
