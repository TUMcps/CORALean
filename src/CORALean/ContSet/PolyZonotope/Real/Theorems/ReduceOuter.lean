import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `PolyZonotope.reduce` over-approximates the set

`reduceBy_outer` is the whole argument, and it holds at *every* partition, which
is what lets the ranking be a heuristic — Girard's metric appears nowhere below.

The factors are untouched, so the same `a` reads both sides and only the
independent coefficients are extended. Kept generators keep their exponent
columns; the dropped ones contribute `D` in row `i`, which the diagonal block
reproduces with coefficient `D / R` for `R` that row's box radius.
`abs_monomial_le_one` is what bounds `|D|` by `R` — a monomial is no larger than
an independent coefficient, which is exactly why the dropped block may become
one — and `Zonotope.coefficient` handles the rescaling, degenerate `R = 0`
included.

`Partition.sum_split₂` is where the partition pays: the sum over all dependent
generators splits into kept and dropped with no side condition.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n d r : ℕ}

/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {PZ : PolyZonotope (Vec ℝ n)}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin r)} (f : Fin (PZ.q + n) → ℝ) :
    ∑ j : Fin (PZ.reduceBy part).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd PZ.q j) :=
  Fin.sum_univ_add f

/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (PZ.reduceBy part).h` and one over `Fin d` as two
atoms, defeq or not. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_h {PZ : PolyZonotope (Vec ℝ n)}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin r)} (f : Fin d → ℝ) :
    ∑ l : Fin (PZ.reduceBy part).h, f l = ∑ l, f l :=
  rfl

/-- Boxing what a partition drops over-approximates, whichever partition it
is. -/
theorem PolyZonotope.reduceBy_outer (PZ : PolyZonotope (Vec ℝ n))
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) :
    PZ.construct ⊆ (PZ.reduceBy part).construct := by
  intro x hxmem
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hxmem
  have hbound : ∀ i,
      |∑ l, PZ.G (part.right l) i * PolyZonotope.monomial PZ.E a (part.right l)|
        ≤ ∑ l, |PZ.G (part.right l) i| := by
    intro i
    calc |∑ l, PZ.G (part.right l) i * PolyZonotope.monomial PZ.E a (part.right l)|
        ≤ ∑ l, |PZ.G (part.right l) i * PolyZonotope.monomial PZ.E a (part.right l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |PZ.G (part.right l) i|
            * |PolyZonotope.monomial PZ.E a (part.right l)|                := by
          simp_rw [abs_mul]
      _ ≤ ∑ l, |PZ.G (part.right l) i|                                     :=
          Finset.sum_le_sum fun l _ => by
            simpa using mul_le_mul_of_nonneg_left
              (PolyZonotope.abs_monomial_le_one PZ.E ha (part.right l))
              (abs_nonneg (PZ.G (part.right l) i))
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |PZ.G (part.right l) i| :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine PolyZonotope.mem_construct_iff.mpr
    ⟨a, Fin.append β (fun i => Zonotope.coefficient (∑ l, |PZ.G (part.right l) i|)
        (∑ l, PZ.G (part.right l) i * PolyZonotope.monomial PZ.E a (part.right l))),
      ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ j
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun l => PZ.G l i * PolyZonotope.monomial PZ.E a l,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]
    have hmono : ∀ l : Fin d,
        PolyZonotope.monomial (fun k l => PZ.E k (part.left l)) a l
          = PolyZonotope.monomial PZ.E a (part.left l) := fun _ => rfl
    simp only [hmono]
    ring

theorem PolyZonotope.reduceGirard_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  (PolyZonotope.compact_exact PZ).subset.trans
    (PolyZonotope.reduceGirard_outer PZ.compact o)

end CORALean.Real
