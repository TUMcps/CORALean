import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `Zonotope.reduce` over-approximates the zonotope

Girard's metric appears nowhere below. All `reduceGirard` does with it is choose
a partition, and `reduceBy_outer` holds for every partition, which is what lets
the ranking be a heuristic.

That lemma is the argument: kept generators keep their coefficients, and the
dropped ones contribute `D` in row `i`, which the diagonal block reproduces with
coefficient `D / R` where `R` is that row's box radius. `hbound` bounds `|D|` by
`R`, so the coefficient is admissible, and `coefficient` isolates the rescaling
as a fact about reals, including the degenerate `R = 0` case where the same bound
forces `D` to vanish.

`Partition.sum_split₂` is where the partition pays: the sum over all generators
splits into kept and dropped with no side condition.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Real

variable {n q r : ℕ}

/-- `Fin.sum_univ_add` at `reduceBy`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.sum_univ_reduceBy {Z : Zonotope (Vec ℝ n)}
    {part : Split (Fin Z.h) into (Fin q) and (Fin r)} (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduceBy part).h, f j = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f

/-- Boxing what a partition drops over-approximates, whichever partition it is. -/
theorem Zonotope.reduceBy_outer (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceBy part).construct := by
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  have hbound : ∀ i, |∑ l, Z.G (part.right l) i * β (part.right l)|
      ≤ ∑ l, |Z.G (part.right l) i| := by
    intro i
    calc |∑ l, Z.G (part.right l) i * β (part.right l)|
        ≤ ∑ l, |Z.G (part.right l) i * β (part.right l)|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |Z.G (part.right l) i| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |Z.G (part.right l) i|                      := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (Z.G (part.right l) i))
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |Z.G (part.right l) i| :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine Zonotope.mem_construct_iff.mpr
    ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      Zonotope.coefficient (∑ l, |Z.G (part.right l) i|)
        (∑ l, Z.G (part.right l) i * β (part.right l))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun j => Z.G j i * β j, Zonotope.sum_univ_reduceBy]
    simp only [Zonotope.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]

theorem Zonotope.reduceGirard_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Real
