import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `PolyZonotope.reduce` over-approximates the set

The error box is untouched, so `mono_subset` reduces this to the nominal part,
and there the argument is the exact layer's with one substitution: a monomial
plays the part a free coefficient plays for a zonotope. `abs_sum_le_radius`
takes either, needing only `|coefficient| ≤ 1`, so what the dropped generators
reach is the same row sum of absolute values — rounded up, which only enlarges.

Sound at every partition, as over ℝ, so a selection rule owes no proof. That is
what lets `reduceGirard` rank with `le`, which `SoundFloatArithmetic`
constrains not at all, and so what makes the rule computable here and not over
ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.reduceBy_h (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) : (PZ.reduceBy part).h = d := rfl

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_q {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin r)} (f : Fin (PZ.q + n) → ℝ) :
    ∑ j : Fin (PZ.reduceBy part).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd PZ.q j) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (PZ.reduceBy part).h` and one over `Fin d` as two
atoms, defeq or not. -/
theorem PolyZonotope.aux_sum_univ_reduceBy_h {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin r)} (f : Fin d → ℝ) :
    ∑ l : Fin (PZ.reduceBy part).h, f l = ∑ l, f l :=
  rfl

/-- What the absorbed generators contribute, so what the block must cover. The
coefficients are monomials, and `abs_sum_le_radius` asks only that they lie in
`[-1, 1]`. -/
theorem PolyZonotope.abs_absorbed_le_radius (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) {a : Fin PZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, toReal (PZ.G i (part.right l))
        * Real.PolyZonotope.monomial PZ.E a (part.right l)|
      ≤ toReal (radius (fun i l => PZ.G i (part.right l)) i) :=
  abs_sum_le_radius (d := fun i l => PZ.G i (part.right l)) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one PZ.E ha (part.right l)) i

theorem PolyZonotope.aux_reduceBy_nominal (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) :
    nominalSet PZ ⊆ nominalSet (PZ.reduceBy part) := by
  intro x hx'
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  have hbound := PolyZonotope.abs_absorbed_le_radius PZ part ha
  refine PolyZonotope.mem_nominalSet_iff.mpr
    ⟨a, Fin.append β (fun i => Real.Zonotope.coefficient
        (toReal (radius (fun i l => PZ.G i (part.right l)) i))
        (∑ l, toReal (PZ.G i (part.right l))
          * Real.PolyZonotope.monomial PZ.E a (part.right l))),
      ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ j
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound i)) (hbound i)
  · rw [hx i, part.sum_split₂ fun l => toReal (PZ.G i l)
        * Real.PolyZonotope.monomial PZ.E a l,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]
    -- the kept columns are the original ones, so their monomials are too
    have hmono : ∀ l : Fin d,
        Real.PolyZonotope.monomial (fun k l => PZ.E k (part.left l)) a l
          = Real.PolyZonotope.monomial PZ.E a (part.left l) := fun _ => rfl
    simp only [hmono]
    ring

theorem PolyZonotope.reduceBy_outer (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) :
    PZ.construct ⊆ (PZ.reduceBy part).construct :=
  mono_subset (PolyZonotope.aux_reduceBy_nominal PZ part) (subset_refl _)

theorem PolyZonotope.reduceGirard_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  PolyZonotope.reduceGirard_outer PZ o

end CORALean.Float
