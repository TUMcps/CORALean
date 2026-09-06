import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

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

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose exponent columns agree off `k₀`
over-approximates, whichever partition names them. -/
theorem PolyZonotope.relaxExp_outer (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1)) :
    PZ.construct ⊆ (PZ.relaxExp part k₀).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, rfl⟩
  have habs : |PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1)| ≤ (PZ.relaxWidth part k₀ : ℝ) :=
    PolyZonotope.abs_sub_monomial_le PZ.E ha hsim
  have hnn : (0:ℝ) ≤ (PZ.relaxWidth part k₀ : ℝ) := Nat.cast_nonneg _
  -- the new independent generator answers the drift with one coefficient
  set t := Zonotope.coefficient (PZ.relaxWidth part k₀ : ℝ)
    (PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1)) with ht
  have hcoef : t * (PZ.relaxWidth part k₀ : ℝ) = PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1) := by
    rw [ht, mul_comm]
    exact Zonotope.mul_coefficient habs
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (PZ.relaxExp part k₀).E a (Fin.castAdd 1 l)
      = PolyZonotope.monomial PZ.E a (part.left l) := fun l => by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_left]
    rfl
  have hlast : PolyZonotope.monomial (PZ.relaxExp part k₀).E a (Fin.natAdd d 0)
      = PolyZonotope.monomial PZ.E a (part.right 1) := by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExp, Fin.append_right]
    rfl
  -- the same factors read both sides, with one coefficient appended
  refine ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one hnn habs
  show PZ.c + ∑ l, PolyZonotope.monomial PZ.E a l • PZ.G l + ∑ j, β j • PZ.GI j
      = PZ.c + (∑ l : Fin (d + 1),
          PolyZonotope.monomial (PZ.relaxExp part k₀).E a l • (PZ.relaxExp part k₀).G l)
        + ∑ j : Fin (PZ.q + 1), Fin.append β (fun _ => t) j • (PZ.relaxExp part k₀).GI j
  rw [part.sum_split₂ fun l => PolyZonotope.monomial PZ.E a l • PZ.G l,
    Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [Fin.sum_univ_one, hmono, hlast]
  simp only [PolyZonotope.relaxExp, Fin.append_left, Fin.append_right]
  -- the drift is what the new generator carries, and the rest cancels
  rw [smul_add, smul_smul, hcoef, sub_smul]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
