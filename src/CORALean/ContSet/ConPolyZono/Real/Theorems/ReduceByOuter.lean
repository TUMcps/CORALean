module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceBy
public import CORALean.ContSet.ConPolyZono.Real.Operations.DropRadius
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# Boxing what two partitions drop over-approximates

The whole argument behind the reduction rule here, and it holds at *every* pair
of partitions, which is what lets the ranking be a heuristic — Girard's metric
appears nowhere below.

The constraint is what a `PolyZonotope` does not have to carry, and it costs
nothing: `p`, `A`, `b` and `R` are copied, so the very witness `a` that
satisfied the old system satisfies the new one, and only the value equation has
work in it. Kept generators keep their exponent columns; the dropped ones of
either block contribute `D` in row `i`, which the diagonal block reproduces with
coefficient `D / R` for `R` that row's box radius. `abs_monomial_le_one` bounds
the dependent half of `|D|` — which is why the two halves may share one box —
and `Zonotope.coefficient` handles the rescaling, degenerate `R = 0` included.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem ConPolyZono.aux_sum_univ_reduceBy_qI {cPZ : ConPolyZono (Vec ℝ n)}
    {partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (cPZ.reduceBy partD partI).qI, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (cPZ.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
theorem ConPolyZono.aux_sum_univ_reduceBy_h {cPZ : ConPolyZono (Vec ℝ n)}
    {partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (cPZ.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl

/-- What the dropped dependent generators contribute: a monomial scales each,
and never by more than one. -/
theorem ConPolyZono.aux_abs_droppedDep_le (cPZ : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r)) {a : Fin cPZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, cPZ.G (partD.right l) i * PolyZonotope.monomial cPZ.E a (partD.right l)|
      ≤ ∑ l, |cPZ.G (partD.right l) i| :=
  calc |∑ l, cPZ.G (partD.right l) i * PolyZonotope.monomial cPZ.E a (partD.right l)|
      ≤ ∑ l, |cPZ.G (partD.right l) i * PolyZonotope.monomial cPZ.E a (partD.right l)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l,
      |cPZ.G (partD.right l) i|
        * |PolyZonotope.monomial cPZ.E a (partD.right l)| := by -- --- PROOF ---
        simp_rw [abs_mul]
    _ ≤ ∑ l, |cPZ.G (partD.right l) i| :=
        Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left
            (PolyZonotope.abs_monomial_le_one cPZ.E ha (partD.right l))
            (abs_nonneg (cPZ.G (partD.right l) i))

/-- The same for the dropped independent generators, where the coefficient is
already free. -/
theorem ConPolyZono.aux_abs_droppedInd_le (cPZ : ConPolyZono (Vec ℝ n))
    (partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)) {β : Fin cPZ.qI → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, cPZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |cPZ.GI (partI.right j) i| :=
  calc |∑ j, cPZ.GI (partI.right j) i * β (partI.right j)|
      ≤ ∑ j, |cPZ.GI (partI.right j) i * β (partI.right j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |cPZ.GI (partI.right j) i| * |β (partI.right j)| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |cPZ.GI (partI.right j) i| :=
        Finset.sum_le_sum fun j _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (partI.right j))
            (abs_nonneg (cPZ.GI (partI.right j) i))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Boxing what the two partitions drop over-approximates, whichever partitions
they are. -/
theorem ConPolyZono.reduceBy_outer (cPZ : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)) :
    cPZ.construct ⊆ (cPZ.reduceBy partD partI).construct := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨a, β, ha, hβ, hsat, hx⟩ := ConPolyZono.mem_construct_iff.mp hxmem
  have hbound : ∀ i,
      |(∑ l, cPZ.G (partD.right l) i * PolyZonotope.monomial cPZ.E a (partD.right l))
          + ∑ j, cPZ.GI (partI.right j) i * β (partI.right j)|
        ≤ cPZ.dropRadius partD partI i :=
    fun i => (abs_add_le _ _).trans (add_le_add
      (ConPolyZono.aux_abs_droppedDep_le cPZ partD ha i)
      (ConPolyZono.aux_abs_droppedInd_le cPZ partI hβ i))
  have hnonneg : ∀ i, (0:ℝ) ≤ cPZ.dropRadius partD partI i :=
    fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: the same factors, plus one coefficient per coordinate scaled to the box
  refine ConPolyZono.mem_construct_iff.mpr
    ⟨a, Fin.append (fun j => β (partI.left j))
        (fun i => Zonotope.coefficient (cPZ.dropRadius partD partI i)
          ((∑ l, cPZ.G (partD.right l) i * PolyZonotope.monomial cPZ.E a (partD.right l))
            + ∑ j, cPZ.GI (partI.right j) i * β (partI.right j))),
      ha, ?_, hsat, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  -- the value: the kept columns unchanged, the dropped ones inside the new box
  · rw [hx i, partD.sum_split₂ fun l => cPZ.G l i * PolyZonotope.monomial cPZ.E a l,
      partI.sum_split₂ fun j => cPZ.GI j i * β j,
      ConPolyZono.aux_sum_univ_reduceBy_qI, ConPolyZono.aux_sum_univ_reduceBy_h]
    simp only [ConPolyZono.reduceBy, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (hbound i)]
    have hmono : ∀ l : Fin d,
        PolyZonotope.monomial (fun k l => cPZ.E k (partD.left l)) a l
          = PolyZonotope.monomial cPZ.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
