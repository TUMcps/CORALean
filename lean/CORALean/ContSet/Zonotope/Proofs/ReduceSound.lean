import CORALean.ContSet.Zonotope.API

/-!
# `Zonotope.reduce` over-approximates the zonotope

Kept generators keep their coefficients. The dropped ones contribute `D` in row
`i`, which the diagonal block reproduces with coefficient `D / R` where `R` is
that row's box radius; `hbound` bounds `|D|` by `R`, so the coefficient is
admissible.

`hcoef` and `hbox` isolate that rescaling as two facts about reals, including
the degenerate `R = 0` case, where the same bound forces `D` to vanish.

`Partition.sum_split₂` is where the partition pays: the sum over all generators
splits into kept and dropped with no side condition.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Zonotope.Proofs

variable {n h q r : ℕ}

theorem reduce_sound (Z : Zonotope n h) (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct := by
  rintro x ⟨β, hβ, hx⟩
  have hcoef : ∀ R D : ℝ, 0 ≤ R → |D| ≤ R → |if R = 0 then 0 else D / R| ≤ 1 := by
    intro R D hR hDR
    split
    · simp
    · rw [abs_div, abs_of_nonneg hR, div_le_one (lt_of_le_of_ne hR (by tauto))]
      exact hDR
  have hbox : ∀ R D : ℝ, |D| ≤ R → R * (if R = 0 then 0 else D / R) = D := by
    intro R D hDR
    by_cases h0 : R = 0
    · simp only [h0, if_pos, zero_mul]
      exact (abs_eq_zero.mp (le_antisymm (h0 ▸ hDR) (abs_nonneg _))).symm
    · rw [if_neg h0]; field_simp
  have hdiag : ∀ (v g : Vec n) (i : Fin n),
      ∑ i', Matrix.diagonal v i i' * g i' = v i * g i := by
    intro v g i
    rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne' _ hb, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hbound : ∀ i, |∑ l, Z.G i (part.right l) * β (part.right l)|
      ≤ ∑ l, |Z.G i (part.right l)| := by
    intro i
    calc |∑ l, Z.G i (part.right l) * β (part.right l)|
        ≤ ∑ l, |Z.G i (part.right l) * β (part.right l)|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |Z.G i (part.right l)| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |Z.G i (part.right l)|                      := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (Z.G i (part.right l)))
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |Z.G i (part.right l)| :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      if (∑ l, |Z.G i (part.right l)|) = 0 then 0
      else (∑ l, Z.G i (part.right l) * β (part.right l)) / ∑ l, |Z.G i (part.right l)|),
    ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact hcoef _ _ (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun j => Z.G i j * β j]
    simp only [Zonotope.reduce, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rw [hdiag, hbox _ _ (hbound i)]

end CORALean.Zonotope.Proofs
