import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsDroppedLeDropRadius
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# `reduceBy` over-approximates, dropping a chosen pair of blocks

The error box is untouched, so `mono_subset` reduces this to the nominal part.
The dropped columns become one diagonal block, at the coefficient
`abs_dropped_le_dropRadius` says reaches them, and the kept columns are the
original ones.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceBy_outer (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) :
    PZ.construct ⊆ (PZ.reduceBy partD partI).construct :=
  mono_subset (PolyZonotope.aux_reduceBy_nominal PZ partD partI) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
