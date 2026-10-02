import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeSum
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import Mathlib.Tactic.Abel

/-!
# Relaxing the exponents of any two generators over-approximates

`[1, Prop. 4]`. The proof is `relaxExp_outer`'s with one bound exchanged:
`abs_sub_monomial_le_sum` replaces `abs_sub_monomial_le`, and it asks nothing of
the two exponent columns, so neither does this. The factors are untouched, the
same `a` reads both sides, and the whole cost of the merge is the drift between
the two monomials, which the summed width bounds.

That the hypothesis is gone is the point of the multi-index width rather than an
accident of the proof: at columns agreeing off `k₀` the sum collapses to the one
`eDiff` `relaxExp` pays, and at columns differing everywhere it is the price of
merging them anyway.

The new independent generator is the summed `ξ_E` times the first of the two, so
the drift asks one scalar of it, `Zonotope.coefficient`, degenerate `ξ_E = 0`
included — one scalar for the whole generator, which is why this holds over any
module.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging any two dependent generators over-approximates, whichever partition
names them: the summed width pays for every exponent that moves. -/
theorem PolyZonotope.relaxExpMulti_outer (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) :
    pZ.construct ⊆ (pZ.relaxExpMulti part).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, rfl⟩
  have hcast : (pZ.relaxWidthMulti part : ℝ)
      = ∑ k, (PolyZonotope.eDiff (pZ.E k (part.right 0)) (pZ.E k (part.right 1)) : ℝ) := by
    rw [PolyZonotope.relaxWidthMulti, Nat.cast_sum]
  have habs : |PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1)| ≤ (pZ.relaxWidthMulti part : ℝ) := by
    rw [hcast]
    exact PolyZonotope.abs_sub_monomial_le_sum pZ.E ha _ _
  have hnn : (0:ℝ) ≤ (pZ.relaxWidthMulti part : ℝ) := Nat.cast_nonneg _
  -- the new independent generator answers the drift with one coefficient
  set t := Zonotope.coefficient (pZ.relaxWidthMulti part : ℝ)
    (PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1)) with ht
  have hcoef : t * (pZ.relaxWidthMulti part : ℝ) = PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1) := by
    rw [ht, mul_comm]
    exact Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (pZ.relaxExpMulti part).E a (Fin.castAdd 1 l)
      = PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_left]
    rfl
  have hlast : PolyZonotope.monomial (pZ.relaxExpMulti part).E a (Fin.natAdd d 0)
      = PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpMulti, Fin.append_right]
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
          PolyZonotope.monomial (pZ.relaxExpMulti part).E a l • (pZ.relaxExpMulti part).G l)
        + ∑ j : Fin (pZ.q + 1), Fin.append β (fun _ => t) j • (pZ.relaxExpMulti part).GI j
  rw [part.sum_split₂ fun l => PolyZonotope.monomial pZ.E a l • pZ.G l,
    Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [Fin.sum_univ_one, hmono, hlast]
  simp only [PolyZonotope.relaxExpMulti, Fin.append_left, Fin.append_right]
  -- the drift is what the new generator carries, and the rest cancels
  rw [smul_add, smul_smul, hcoef, sub_smul]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
