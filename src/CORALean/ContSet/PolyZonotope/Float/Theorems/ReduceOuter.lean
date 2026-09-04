import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.Monomial
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `PolyZonotope.reduce` over-approximates the set

The error box is untouched, so `mono_subset` reduces this to the nominal part,
and there the argument is the exact layer's with one substitution: a monomial
plays the part a free coefficient plays for a zonotope. `abs_sum_le_radius`
takes either, needing only `|coefficient| ≤ 1`, so what the dropped generators
of both blocks reach is the same row sum of absolute values — rounded up, and
added upward again to merge the two, which only enlarges.

Sound at every pair of partitions, as over ℝ, so a selection rule owes no proof.
That is what lets `reduceGirard` rank with `le`, which `SoundFloatArithmetic`
constrains not at all, and so what makes the rule computable here and not over
ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.reduceBy_h (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) :
    (PZ.reduceBy partD partI).h = d := rfl

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {PZ : PolyZonotope 𝕋 n}
    {partD : Split (Fin PZ.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (PZ.reduceBy partD partI).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (PZ.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_h {PZ : PolyZonotope 𝕋 n}
    {partD : Split (Fin PZ.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (PZ.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl

/-- What the dropped dependent generators contribute, so what the block must
cover. The coefficients are monomials, and `abs_sum_le_radius` asks only that
they lie in `[-1, 1]`. -/
theorem PolyZonotope.aux_abs_droppedDep_le (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r)) {a : Fin PZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, toReal (PZ.G i (partD.right l))
        * Real.PolyZonotope.monomial PZ.E a (partD.right l)|
      ≤ toReal (radius (fun i l => PZ.G i (partD.right l)) i) :=
  abs_sum_le_radius (d := fun i l => PZ.G i (partD.right l)) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one PZ.E ha (partD.right l)) i

/-- The same for the dropped independent generators, whose coefficients are
free to begin with. -/
theorem PolyZonotope.aux_abs_droppedInd_le (PZ : PolyZonotope 𝕋 n)
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) {β : Fin PZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, toReal (PZ.GI i (partI.right j)) * β (partI.right j)|
      ≤ toReal (radius (fun i j => PZ.GI i (partI.right j)) i) :=
  abs_sum_le_radius (d := fun i j => PZ.GI i (partI.right j)) (fun _ _ => le_refl _)
    (fun j => hβ (partI.right j)) i

/-- One box for the two dropped blocks: their radii, added upward. -/
theorem PolyZonotope.abs_dropped_le_dropRadius (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) {a : Fin PZ.p → ℝ}
    {β : Fin PZ.q → ℝ} (ha : ∀ k, |a k| ≤ 1) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |(∑ l, toReal (PZ.G i (partD.right l))
          * Real.PolyZonotope.monomial PZ.E a (partD.right l))
        + ∑ j, toReal (PZ.GI i (partI.right j)) * β (partI.right j)|
      ≤ toReal (PZ.dropRadius partD partI i) := by
  have hD := PolyZonotope.aux_abs_droppedDep_le PZ partD ha i
  have hI := PolyZonotope.aux_abs_droppedInd_le PZ partI hβ i
  have hsum := add_le_addUp (radius (fun i l => PZ.G i (partD.right l)) i)
    (radius (fun i j => PZ.GI i (partI.right j)) i)
  refine le_trans (abs_add_le _ _) ?_
  simp only [PolyZonotope.dropRadius]
  linarith

-- the dropped columns become one diagonal block, at the coefficient that reaches them
theorem PolyZonotope.aux_reduceBy_nominal (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) :
    nominalSet PZ ⊆ nominalSet (PZ.reduceBy partD partI) := by
  intro x hx'
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  have hbound := PolyZonotope.abs_dropped_le_dropRadius PZ partD partI ha hβ
  refine PolyZonotope.mem_nominalSet_iff.mpr
    ⟨a, Fin.append (fun j => β (partI.left j)) (fun i => Real.Zonotope.coefficient
        (toReal (PZ.dropRadius partD partI i))
        ((∑ l, toReal (PZ.G i (partD.right l))
            * Real.PolyZonotope.monomial PZ.E a (partD.right l))
          + ∑ j, toReal (PZ.GI i (partI.right j)) * β (partI.right j))),
      ha, ?_, fun i => ?_⟩
  -- the kept coefficients are unchanged; the fresh ones are scaled to that box
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound i)) (hbound i)
  · rw [hx i, partD.sum_split₂ fun l => toReal (PZ.G i l)
        * Real.PolyZonotope.monomial PZ.E a l,
      partI.sum_split₂ fun j => toReal (PZ.GI i j) * β j,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]
    -- the kept columns are the original ones, so their monomials are too
    have hmono : ∀ l : Fin d,
        Real.PolyZonotope.monomial (fun k l => PZ.E k (partD.left l)) a l
          = Real.PolyZonotope.monomial PZ.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring

theorem PolyZonotope.reduceBy_outer (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) :
    PZ.construct ⊆ (PZ.reduceBy partD partI).construct :=
  mono_subset (PolyZonotope.aux_reduceBy_nominal PZ partD partI) (subset_refl _)

theorem PolyZonotope.reduceGirard_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  subset_trans (PolyZonotope.compact_outer PZ)
    (PolyZonotope.reduceGirard_outer PZ.compact o)

theorem PolyZonotope.reduceGirardDependent_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirardDependent o).construct := by
  unfold PolyZonotope.reduceGirardDependent
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

/-- The tighter rule is sound on the same line as the bounded one, which is the
point of `reduceBy_outer` holding at every pair of partitions: what separates
the two is the order bound and nothing here. -/
theorem PolyZonotope.reduceDependent_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceDependent o).construct :=
  subset_trans (PolyZonotope.compact_outer PZ)
    (PolyZonotope.reduceGirardDependent_outer PZ.compact o)

end CORALean.Float
