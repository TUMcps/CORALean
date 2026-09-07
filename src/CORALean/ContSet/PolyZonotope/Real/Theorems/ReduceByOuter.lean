import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

/-!
# Boxing what two partitions drop over-approximates

The whole argument behind every reduction rule here, and it holds at *every*
pair of partitions, which is what lets the ranking be a heuristic — Girard's
metric appears nowhere below.

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
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {pZ : PolyZonotope (Vec ℝ n)}
    {partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (pZ.reduceBy partD partI).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (pZ.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_h {pZ : PolyZonotope (Vec ℝ n)}
    {partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (pZ.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl

/-- What the dropped dependent generators contribute: a monomial scales each,
and never by more than one. -/
theorem PolyZonotope.aux_abs_droppedDep_le (pZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l)|
      ≤ ∑ l, |pZ.G (partD.right l) i| :=
  calc |∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l)|
      ≤ ∑ l, |pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |pZ.G (partD.right l)
      i| * |PolyZonotope.monomial pZ.E a (partD.right l)| := by -- --- PROOF ---
        simp_rw [abs_mul]
    _ ≤ ∑ l, |pZ.G (partD.right l) i| :=
        Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left
            (PolyZonotope.abs_monomial_le_one pZ.E ha (partD.right l))
            (abs_nonneg (pZ.G (partD.right l) i))

/-- The same for the dropped independent generators, where the coefficient is
already free. -/
theorem PolyZonotope.aux_abs_droppedInd_le (pZ : PolyZonotope (Vec ℝ n))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {β : Fin pZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, pZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |pZ.GI (partI.right j) i| :=
  calc |∑ j, pZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |pZ.GI (partI.right j) i * β (partI.right j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |pZ.GI (partI.right j) i| * |β (partI.right j)| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |pZ.GI (partI.right j) i| :=
        Finset.sum_le_sum fun j _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (partI.right j))
            (abs_nonneg (pZ.GI (partI.right j) i))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what the two partitions drop over-approximates, whichever partitions
they are. -/
theorem PolyZonotope.reduceBy_outer (pZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) :
    pZ.construct ⊆ (pZ.reduceBy partD partI).construct := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hxmem
  have hbound : ∀ i,
      |(∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l))
          + ∑ j, pZ.GI (partI.right j) i * β (partI.right j)|
        ≤ pZ.dropRadius partD partI i :=
    fun i => (abs_add_le _ _).trans (add_le_add
      (PolyZonotope.aux_abs_droppedDep_le pZ partD ha i)
      (PolyZonotope.aux_abs_droppedInd_le pZ partI hβ i))
  have hnonneg : ∀ i, (0:ℝ) ≤ pZ.dropRadius partD partI i :=
    fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: the kept coefficients, plus one per coordinate scaled to the dropped reach
  refine PolyZonotope.mem_construct_iff.mpr
    ⟨a, Fin.append (fun j => β (partI.left j))
        (fun i => Zonotope.coefficient (pZ.dropRadius partD partI i)
          ((∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l))
            + ∑ j, pZ.GI (partI.right j) i * β (partI.right j))),
      ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  -- the value: the kept columns unchanged, the dropped ones inside the new box
  · rw [hx i, partD.sum_split₂ fun l => pZ.G l i * PolyZonotope.monomial pZ.E a l,
      partI.sum_split₂ fun j => pZ.GI j i * β j,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]
    have hmono : ∀ l : Fin d,
        PolyZonotope.monomial (fun k l => pZ.E k (partD.left l)) a l
          = PolyZonotope.monomial pZ.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
