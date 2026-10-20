module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# Boxing what two partitions drop keeps every dependency

The argument behind every reduction rule here, holding at *every* pair of partitions, which
lets the ranking be a heuristic. `reduceBy_outer` is this at the whole factor box. The factors
are untouched, so the same `a` reads both sides: an enclosure of each evaluation separately,
which [1, Lemma 4] needs and never states. Kept generators keep their exponent columns; the
dropped ones contribute `D` in row `i`, which the diagonal block reproduces with coefficient
`D / R`. `abs_monomial_le_one` bounds the dependent half of `|D|`, and `Zonotope.coefficient`
rescales, degenerate `R = 0` included.

## Inputs
* `pZ` – polynomial zonotope
* `partD` – split of the dependent generators
* `partI` – split of the independent generators
* `B` – box of factor values

## Hypotheses
* `hB` – factor values are at most one

## Conclusion
* evaluation on the box is preserved

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `mem_construct_iff` at an evaluation: one coordinate of the defining
equation, both generator blocks transposed. -/
theorem PolyZonotope.aux_mem_evalOn_iff {pZ : PolyZonotope (Vec ℝ n)}
    {B : Set (Fin pZ.p → ℝ)} {x : Vec ℝ n} : -- --- CONCL ---
    x ∈ pZ.evalOn B ↔ ∃ a ∈ B, ∃ β : Fin pZ.q → ℝ, (∀ j, |β j| ≤ 1)
      ∧ ∀ i, x i = pZ.c i + (∑ l, pZ.G l i * PolyZonotope.monomial pZ.E a l)
            + ∑ j, pZ.GI j i * β j := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ) (i : Fin n),
      (pZ.point a + ∑ j, β j • pZ.GI j) i
        = pZ.c i + (∑ l, pZ.G l i * PolyZonotope.monomial pZ.E a l)
            + ∑ j, pZ.GI j i * β j := by
    intro a β i
    show (pZ.c + ∑ l, PolyZonotope.monomial pZ.E a l • pZ.G l + ∑ j, β j • pZ.GI j) i = _
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  constructor
  · rintro ⟨a, ha, β, hβ, rfl⟩
    exact ⟨a, ha, β, hβ, key a β⟩
  · rintro ⟨a, ha, β, hβ, hx⟩
    exact ⟨a, ha, β, hβ, funext fun i => (hx i).trans (key a β i).symm⟩


/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {pZ : PolyZonotope (Vec ℝ n)}
    {partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)} (f : Fin (dI + n) → ℝ) : -- --- CONCL ---
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
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) : -- --- CONCL ---
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
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
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

/-- Boxing what the two partitions drop encloses every evaluation of the
original, at the very same factor vector. -/
theorem PolyZonotope.reduceBy_evalOn (pZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {B : Set (Fin pZ.p → ℝ)}
    (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) : -- --- CONCL ---
    pZ.evalOn B ⊆ (pZ.reduceBy partD partI).evalOn B := by -- --- PROOF ---
  intro x hxmem
  obtain ⟨a, haB, β, hβ, hx⟩ := PolyZonotope.aux_mem_evalOn_iff.mp hxmem
  have ha : ∀ k, |a k| ≤ 1 := hB a haB
  have hbound : ∀ i,
      |(∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l))
          + ∑ j, pZ.GI (partI.right j) i * β (partI.right j)|
        ≤ pZ.dropRadius partD partI i :=
    fun i => (abs_add_le _ _).trans (add_le_add
      (PolyZonotope.aux_abs_droppedDep_le pZ partD ha i)
      (PolyZonotope.aux_abs_droppedInd_le pZ partI hβ i))
  have hnonneg : ∀ i, (0:ℝ) ≤ pZ.dropRadius partD partI i :=
    fun i => (abs_nonneg _).trans (hbound i)
  -- the witness: the same factors, the kept coefficients, and one per coordinate
  refine PolyZonotope.aux_mem_evalOn_iff.mpr
    ⟨a, haB, Fin.append (fun j => β (partI.left j))
        (fun i => Zonotope.coefficient (pZ.dropRadius partD partI i)
          ((∑ l, pZ.G (partD.right l) i * PolyZonotope.monomial pZ.E a (partD.right l))
            + ∑ j, pZ.GI (partI.right j) i * β (partI.right j))),
      ?_, fun i => ?_⟩
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
