import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonpos
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

/-!
# The recentred relaxation over-approximates

`relaxExp_outer` with the drift read as a midpoint and a radius instead of as a
symmetric bound. `abs_sub_monomial_le` gives `|δ| ≤ ξ_E` and
`sub_monomial_nonpos` gives `δ ≤ 0`, so `δ + ξ_E/2` is within `ξ_E/2` of zero
and `Zonotope.coefficient` answers for it at half the generator.

The three extra hypotheses are exactly what makes the drift one-sided, and they
are what `[1, Thm. 1]` states incompletely: it asks only that column `i` be
even. The generator graph of `[1, Def. 5]` supplies all three — it admits an edge
only at equal parity and from the higher exponent to the lower — so the algorithm
never meets the gap, only the theorem does.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}

/-- Merging two generators whose columns agree off `k₀`, with column `i` even,
`E_{k₀,j}` even and `E_{k₀,j} ≤ E_{k₀,i}`, over-approximates. -/
theorem PolyZonotope.relaxExpEven_outer (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1))
    (heven : ∀ k, Even (PZ.E k (part.right 0)))
    (hevenj : Even (PZ.E k₀ (part.right 1)))
    (hle : PZ.E k₀ (part.right 1) ≤ PZ.E k₀ (part.right 0)) :
    PZ.construct ⊆ (PZ.relaxExpEven part k₀).construct := by
  rintro x ⟨a, β, ha, hβ, rfl⟩
  have habs : |PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1)| ≤ (PZ.relaxWidth part k₀ : ℝ) :=
    PolyZonotope.abs_sub_monomial_le PZ.E ha hsim
  have hsign : PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1) ≤ 0 :=
    PolyZonotope.sub_monomial_nonpos PZ.E ha hsim heven hevenj hle
  have hnn : (0:ℝ) ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 := by
    have h := Nat.cast_nonneg (α := ℝ) (PZ.relaxWidth part k₀)
    linarith
  -- one-sided drift: its midpoint is `-ξ_E/2` and its radius `ξ_E/2`
  have hmid : |PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1) + (PZ.relaxWidth part k₀ : ℝ) / 2|
        ≤ (PZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [abs_le] at habs ⊢
    constructor <;> linarith [habs.1, habs.2]
  set t := Zonotope.coefficient ((PZ.relaxWidth part k₀ : ℝ) / 2)
    (PolyZonotope.monomial PZ.E a (part.right 0)
      - PolyZonotope.monomial PZ.E a (part.right 1) + (PZ.relaxWidth part k₀ : ℝ) / 2) with ht
  have hcoef : t * ((PZ.relaxWidth part k₀ : ℝ) / 2)
      = PolyZonotope.monomial PZ.E a (part.right 0)
        - PolyZonotope.monomial PZ.E a (part.right 1) + (PZ.relaxWidth part k₀ : ℝ) / 2 := by
    rw [ht, mul_comm]
    exact Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (PZ.relaxExpEven part k₀).E a (Fin.castAdd 1 l)
      = PolyZonotope.monomial PZ.E a (part.left l) := fun l => by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_left]
    rfl
  have hlast : PolyZonotope.monomial (PZ.relaxExpEven part k₀).E a (Fin.natAdd d 0)
      = PolyZonotope.monomial PZ.E a (part.right 1) := by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpEven, Fin.append_right]
    rfl
  -- the same factors read both sides, with one coefficient appended
  refine ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one hnn hmid
  show PZ.c + ∑ l, PolyZonotope.monomial PZ.E a l • PZ.G l + ∑ j, β j • PZ.GI j
      = PZ.c - ((PZ.relaxWidth part k₀ : ℝ) / 2) • PZ.G (part.right 0)
          + (∑ l : Fin (d + 1), PolyZonotope.monomial (PZ.relaxExpEven part k₀).E a l
              • (PZ.relaxExpEven part k₀).G l)
        + ∑ j : Fin (PZ.q + 1), Fin.append β (fun _ => t) j • (PZ.relaxExpEven part k₀).GI j
  rw [part.sum_split₂ fun l => PolyZonotope.monomial PZ.E a l • PZ.G l,
    Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [Fin.sum_univ_one, hmono, hlast]
  simp only [PolyZonotope.relaxExpEven, Fin.append_left, Fin.append_right]
  -- half the drift sits in the centre and half in the new generator
  rw [smul_add, smul_smul, hcoef, add_smul, sub_smul]
  abel

end CORALean.Real
