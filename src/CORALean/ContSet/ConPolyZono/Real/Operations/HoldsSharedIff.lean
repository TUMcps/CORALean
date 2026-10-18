module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight

@[expose] public section

/-!
# Two constraint systems stacked over the same factors

`holds_plus_iff` lays two systems out over *disjoint* factor blocks. This lays
them out over one shared block: the rows still split block-diagonally, but both
systems read the same factors, so the exponent matrices are concatenated by
`appendE` rather than block-diagonalized by `plusE`.

That is the shape [1, Thm. 1]'s constraint matrix has — its selector rows and its
two operand row blocks all read the same `p₁ + p₂ + 2` factors — and the split
is exact because a row of one block still meets only its own columns.

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

theorem ConPolyZono.holds_shared_iff {p m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (b₁ : Interval (Vec ℝ m₁)) (R₁ : Fin p → Fin q₁ → ℕ) (A₂ : Mat ℝ m₂ q₂)
    (b₂ : Interval (Vec ℝ m₂)) (R₂ : Fin p → Fin q₂ → ℕ) (a : Fin p → ℝ) : -- --- STMT ---
    ConPolyZono.holds (ConPolyZono.plusA A₁ A₂) (ConPolyZono.plusB b₁ b₂)
        (ConPolyZono.appendE R₁ R₂) a
      ↔ ConPolyZono.holds A₁ b₁ R₁ a ∧ ConPolyZono.holds A₂ b₂ R₂ a := by -- --- PROOF ---
  have hL : ∀ i : Fin m₁,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a)
          (Fin.castAdd m₂ i)
        = (A₁ *ᵥ PolyZonotope.monomial R₁ a) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a
        (Fin.castAdd q₂ l)) = PolyZonotope.monomial R₁ a :=
      funext fun l => ConPolyZono.monomial_appendE_left R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_left, hm]
  -- the mirror on the right block, its monomials read off the same factors
  have hR : ∀ i : Fin m₂,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a)
          (Fin.natAdd m₁ i)
        = (A₂ *ᵥ PolyZonotope.monomial R₂ a) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a
        (Fin.natAdd q₁ l)) = PolyZonotope.monomial R₂ a :=
      funext fun l => ConPolyZono.monomial_appendE_right R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_right, hm]
  -- both directions, `plusB` splitting the bounds the way the rows split
  constructor
  · intro hsat
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h := hsat (Fin.castAdd m₂ i)
      rw [hL i] at h
      simpa only [ConPolyZono.plusB, Fin.append_left] using h
    · have h := hsat (Fin.natAdd m₁ i)
      rw [hR i] at h
      simpa only [ConPolyZono.plusB, Fin.append_right] using h
  · rintro ⟨h₁, h₂⟩
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hL i]
      simpa only [ConPolyZono.plusB, Fin.append_left] using h₁ i
    · rw [hR i]
      simpa only [ConPolyZono.plusB, Fin.append_right] using h₂ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
