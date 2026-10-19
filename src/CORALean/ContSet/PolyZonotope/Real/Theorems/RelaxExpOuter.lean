module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeEDiffTight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EDiffTightNonneg
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Relaxing the exponents of two similar generators over-approximates

`[1, Thm. 1]` at `ξ_G = ξ_E`. The factors are untouched, so the same `a` reads
both sides, and everything the merge costs sits in one term: the two monomials
share every factor but the one at `k₀`, so their difference is
`(a_{k₀}^{E_i} - a_{k₀}^{E_j})` times a product that never leaves `[-1,1]`, and
`abs_sub_monomial_le` bounds that by `ξ_E`.

The new independent generator is `ξ_E` times the first of the two, so the
coefficient the difference asks of it is `Zonotope.coefficient`, degenerate
`ξ_E = 0` included — and it is one scalar for the whole generator rather than
one per coordinate, which is why this holds over any module.

The similarity of `[1, Def. 4]` enters as `hsim`, agreement off `k₀`, rather
than as a computed predicate: the operation needs `k₀` itself and not merely its
existence, and agreement is all the proof spends.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose exponent columns agree off `k₀`
over-approximates, whichever partition names them. -/
theorem PolyZonotope.relaxExp_outer (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) :
    pZ.construct ⊆ (pZ.relaxExp part k₀).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, rfl⟩
  have habs : |PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1)| ≤ pZ.relaxWidth part k₀ :=
    PolyZonotope.abs_sub_monomial_le_eDiffTight pZ.E ha hsim
  have hnn : (0:ℝ) ≤ pZ.relaxWidth part k₀ := PolyZonotope.eDiffTight_nonneg _ _
  -- the new independent generator answers the drift with one coefficient
  set t := Zonotope.coefficient (pZ.relaxWidth part k₀)
    (PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1)) with ht
  have hcoef : t * pZ.relaxWidth part k₀ = PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1) := by
    rw [ht, mul_comm]
    exact Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (pZ.relaxExp part k₀).E a (Fin.castAdd 1 l)
      = PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_left]
    rfl
  have hlast : PolyZonotope.monomial (pZ.relaxExp part k₀).E a (Fin.natAdd d 0)
      = PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_right]
    rfl
  -- the same factors read both sides, with one coefficient appended
  refine ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one hnn habs
  show pZ.c + ∑ l, PolyZonotope.monomial pZ.E a l • pZ.G l + ∑ j, β j • pZ.GI j
      = pZ.c + (∑ l : Fin (d + 1),
          PolyZonotope.monomial (pZ.relaxExp part k₀).E a l • (pZ.relaxExp part k₀).G l)
        + ∑ j : Fin (pZ.q + 1), Fin.append β (fun _ => t) j • (pZ.relaxExp part k₀).GI j
  rw [part.sum_split₂ fun l => PolyZonotope.monomial pZ.E a l • pZ.G l,
    Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [Fin.sum_univ_one, hmono, hlast]
  simp only [PolyZonotope.relaxExp, Fin.append_left, Fin.append_right]
  -- the drift is what the new generator carries, and the rest cancels
  rw [smul_add, smul_smul, hcoef, sub_smul]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
