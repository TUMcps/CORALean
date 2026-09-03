import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `PolyZonotope.reduce` over-approximates the set

`reduceBy_outer` is the whole argument, and it holds at *every* pair of
partitions, which is what lets the ranking be a heuristic — Girard's metric
appears nowhere below.

The factors are untouched, so the same `a` reads both sides. Kept generators
keep their exponent columns; the dropped ones of either block contribute `D` in
row `i`, which the diagonal block reproduces with coefficient `D / R` for `R`
that row's box radius. `abs_monomial_le_one` is what bounds the dependent half
of `|D|` — a monomial is no larger than an independent coefficient, which is
exactly why the two halves may share one box — and `Zonotope.coefficient`
handles the rescaling, degenerate `R = 0` included.

`Partition.sum_split₂` is where the partitions pay: each generator sum splits
into kept and dropped with no side condition.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n d r dI rI : ℕ}

/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {PZ : PolyZonotope (Vec ℝ n)}
    {partD : Split (Fin PZ.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (PZ.reduceBy partD partI).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (PZ.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_h {PZ : PolyZonotope (Vec ℝ n)}
    {partD : Split (Fin PZ.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (PZ.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl

/-- What the dropped dependent generators contribute: a monomial scales each,
and never by more than one. -/
theorem PolyZonotope.aux_abs_droppedDep_le (PZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r)) {a : Fin PZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, PZ.G (partD.right l) i * PolyZonotope.monomial PZ.E a (partD.right l)|
      ≤ ∑ l, |PZ.G (partD.right l) i| :=
  calc |∑ l, PZ.G (partD.right l) i * PolyZonotope.monomial PZ.E a (partD.right l)|
      ≤ ∑ l, |PZ.G (partD.right l) i * PolyZonotope.monomial PZ.E a (partD.right l)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |PZ.G (partD.right l) i| * |PolyZonotope.monomial PZ.E a (partD.right l)| := by
        simp_rw [abs_mul]
    _ ≤ ∑ l, |PZ.G (partD.right l) i| :=
        Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left
            (PolyZonotope.abs_monomial_le_one PZ.E ha (partD.right l))
            (abs_nonneg (PZ.G (partD.right l) i))

/-- The same for the dropped independent generators, where the coefficient is
already free. -/
theorem PolyZonotope.aux_abs_droppedInd_le (PZ : PolyZonotope (Vec ℝ n))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) {β : Fin PZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, PZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |PZ.GI (partI.right j) i| :=
  calc |∑ j, PZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |PZ.GI (partI.right j) i * β (partI.right j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |PZ.GI (partI.right j) i| * |β (partI.right j)| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |PZ.GI (partI.right j) i| :=
        Finset.sum_le_sum fun j _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (partI.right j))
            (abs_nonneg (PZ.GI (partI.right j) i))

/-- Boxing what the two partitions drop over-approximates, whichever partitions
they are. -/
theorem PolyZonotope.reduceBy_outer (PZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) :
    PZ.construct ⊆ (PZ.reduceBy partD partI).construct := by
  intro x hxmem
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hxmem
  have hbound : ∀ i,
      |(∑ l, PZ.G (partD.right l) i * PolyZonotope.monomial PZ.E a (partD.right l))
          + ∑ j, PZ.GI (partI.right j) i * β (partI.right j)|
        ≤ PZ.dropRadius partD partI i :=
    fun i => (abs_add_le _ _).trans (add_le_add
      (PolyZonotope.aux_abs_droppedDep_le PZ partD ha i)
      (PolyZonotope.aux_abs_droppedInd_le PZ partI hβ i))
  have hnonneg : ∀ i, (0:ℝ) ≤ PZ.dropRadius partD partI i :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine PolyZonotope.mem_construct_iff.mpr
    ⟨a, Fin.append (fun j => β (partI.left j))
        (fun i => Zonotope.coefficient (PZ.dropRadius partD partI i)
          ((∑ l, PZ.G (partD.right l) i * PolyZonotope.monomial PZ.E a (partD.right l))
            + ∑ j, PZ.GI (partI.right j) i * β (partI.right j))),
      ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, partD.sum_split₂ fun l => PZ.G l i * PolyZonotope.monomial PZ.E a l,
      partI.sum_split₂ fun j => PZ.GI j i * β j,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]
    have hmono : ∀ l : Fin d,
        PolyZonotope.monomial (fun k l => PZ.E k (partD.left l)) a l
          = PolyZonotope.monomial PZ.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring

theorem PolyZonotope.reduceGirard_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  (PolyZonotope.compact_exact PZ).subset.trans
    (PolyZonotope.reduceGirard_outer PZ.compact o)

end CORALean.Real
