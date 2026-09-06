import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# Boxing what two partitions drop encloses

The error box is untouched and so is the constraint block, so `mono_subset`
reduces this to the nominal part and the very witness `a` that satisfied the old
system satisfies the new one. What is left is the exact layer's argument with
one substitution: a monomial plays the part a free coefficient plays for a
zonotope. `abs_sum_le_radius` takes either, needing only `|coefficient| ≤ 1`, so
what the dropped generators of both blocks reach is the same row sum of absolute
values — rounded up, and added upward again to merge the two, which only
enlarges.

Sound at every pair of partitions, as over ℝ, so a selection rule owes no proof.
That is what lets `reduceGirard` rank with `le`, which `SoundFloatArithmetic`
constrains not at all, and so what makes the rule computable here.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
theorem ConPolyZono.aux_sum_univ_reduceBy_q {C : ConPolyZono 𝕋 n}
    {partD : Split (Fin C.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin C.q) into (Fin dI) and (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (C.reduceBy partD partI).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (C.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
theorem ConPolyZono.aux_sum_univ_reduceBy_h {C : ConPolyZono 𝕋 n}
    {partD : Split (Fin C.h) into (Fin d) and (Fin r)}
    {partI : Split (Fin C.q) into (Fin dI) and (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (C.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl

/-- What the dropped dependent generators contribute, so what the box must
cover. The coefficients are monomials, and `abs_sum_le_radius` asks only that
they lie in `[-1, 1]`. -/
theorem ConPolyZono.aux_abs_droppedDep_le (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r)) {a : Fin C.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, toReal (C.G i (partD.right l))
        * Real.PolyZonotope.monomial C.E a (partD.right l)|
      ≤ toReal (radius (fun i l => C.G i (partD.right l)) i) :=
  abs_sum_le_radius (d := fun i l => C.G i (partD.right l)) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one C.E ha (partD.right l)) i

/-- The same for the dropped independent generators, whose coefficients are
free to begin with. -/
theorem ConPolyZono.aux_abs_droppedInd_le (C : ConPolyZono 𝕋 n)
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) {β : Fin C.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, toReal (C.GI i (partI.right j)) * β (partI.right j)|
      ≤ toReal (radius (fun i j => C.GI i (partI.right j)) i) :=
  abs_sum_le_radius (d := fun i j => C.GI i (partI.right j)) (fun _ _ => le_refl _)
    (fun j => hβ (partI.right j)) i

/-- One box for the two dropped blocks: their radii, added upward. -/
theorem ConPolyZono.aux_abs_dropped_le (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) {a : Fin C.p → ℝ}
    {β : Fin C.q → ℝ} (ha : ∀ k, |a k| ≤ 1) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |(∑ l, toReal (C.G i (partD.right l))
          * Real.PolyZonotope.monomial C.E a (partD.right l))
        + ∑ j, toReal (C.GI i (partI.right j)) * β (partI.right j)|
      ≤ toReal (C.dropRadius partD partI i) := by -- --- PROOF ---
  have hD := ConPolyZono.aux_abs_droppedDep_le C partD ha i
  have hI := ConPolyZono.aux_abs_droppedInd_le C partI hβ i
  have hsum := add_le_addUp (radius (fun i l => C.G i (partD.right l)) i)
    (radius (fun i j => C.GI i (partI.right j)) i)
  refine le_trans (abs_add_le _ _) ?_
  simp only [ConPolyZono.dropRadius]
  linarith

-- the dropped columns become one diagonal block, at the coefficient that reaches them
theorem ConPolyZono.aux_reduceBy_nominal (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) :
    nominalSet C ⊆ nominalSet (C.reduceBy partD partI) := by -- --- PROOF ---
  intro x hx'
  obtain ⟨a, β, ha, hβ, hsat, hx⟩ := ConPolyZono.mem_nominalSet_iff.mp hx'
  have hbound := ConPolyZono.aux_abs_dropped_le C partD partI ha hβ
  refine ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, Fin.append (fun j => β (partI.left j)) (fun i => Real.Zonotope.coefficient
        (toReal (C.dropRadius partD partI i))
        ((∑ l, toReal (C.G i (partD.right l))
            * Real.PolyZonotope.monomial C.E a (partD.right l))
          + ∑ j, toReal (C.GI i (partI.right j)) * β (partI.right j))),
      ha, ?_, hsat, fun i => ?_⟩
  -- the kept coefficients are unchanged; the fresh ones are scaled to that box
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound i)) (hbound i)
  · rw [hx i, partD.sum_split₂ fun l => toReal (C.G i l)
        * Real.PolyZonotope.monomial C.E a l,
      partI.sum_split₂ fun j => toReal (C.GI i j) * β j,
      ConPolyZono.aux_sum_univ_reduceBy_q, ConPolyZono.aux_sum_univ_reduceBy_h]
    simp only [ConPolyZono.reduceBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]
    -- the kept columns are the original ones, so their monomials are too
    have hmono : ∀ l : Fin d,
        Real.PolyZonotope.monomial (fun k l => C.E k (partD.left l)) a l
          = Real.PolyZonotope.monomial C.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceBy_outer (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) :
    C.construct ⊆ (C.reduceBy partD partI).construct :=
  mono_subset (ConPolyZono.aux_reduceBy_nominal C partD partI) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
