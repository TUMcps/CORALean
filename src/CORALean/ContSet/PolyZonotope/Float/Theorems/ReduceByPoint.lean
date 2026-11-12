module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

@[expose] public section

/-!
# A point of a polynomial zonotope is a point of its `reduceBy`, at the same factors

The dropped columns become one diagonal block, at the coefficient `aux_abs_dropped_le_dropRadius`
says reaches them, and the kept columns are the original ones; the factor values are untouched,
so the statement serves the fibers as well as the set.

## Inputs
* `pZ` – polynomial zonotope
* `partD` – split of the dependent generators
* `partI` – split of the independent generators
* `a` – factor values
* `β` – independent coefficients

## Hypotheses
* `ha` – the factor values lie in the unit box
* `hβ` – the independent coefficients lie in the unit box

## Conclusion
* new independent coefficients in the unit box give the same point of the reduced set
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the dropped dependent generators contribute, so what the block must
cover. The coefficients are monomials, and `abs_sum_le_radius` asks only that
they lie in `[-1, 1]`. -/
private theorem PolyZonotope.aux_abs_droppedDep_le (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) :
    |∑ l, toReal (pZ.G (partD.right l) i)
        * Real.PolyZonotope.monomial pZ.E a (partD.right l)|
      ≤ toReal (radius (fun i l => pZ.G (partD.right l) i) i) :=
  abs_sum_le_radius (d := fun i l => pZ.G (partD.right l) i) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one pZ.E ha (partD.right l)) i


/-- The same for the dropped independent generators, whose coefficients are
free to begin with. -/
private theorem PolyZonotope.aux_abs_droppedInd_le (pZ : PolyZonotope (Vec 𝕋 n))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {β : Fin pZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ j, toReal (pZ.GI (partI.right j) i) * β (partI.right j)|
      ≤ toReal (radius (fun i j => pZ.GI (partI.right j) i) i) :=
  abs_sum_le_radius (d := fun i j => pZ.GI (partI.right j) i) (fun _ _ => le_refl _)
    (fun j => hβ (partI.right j)) i


/-- One box for the two dropped blocks: their radii, added upward. -/
private theorem PolyZonotope.aux_abs_dropped_le_dropRadius (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {a : Fin pZ.p → ℝ}
    {β : Fin pZ.q → ℝ} (ha : ∀ k, |a k| ≤ 1) (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |(∑ l, toReal (pZ.G (partD.right l) i)
          * Real.PolyZonotope.monomial pZ.E a (partD.right l))
        + ∑ j, toReal (pZ.GI (partI.right j) i) * β (partI.right j)|
      ≤ toReal (pZ.dropRadius partD partI i) := by -- --- PROOF ---
  have hD := PolyZonotope.aux_abs_droppedDep_le pZ partD ha i
  have hI := PolyZonotope.aux_abs_droppedInd_le pZ partI hβ i
  have hsum := add_le_addUp (radius (fun i l => pZ.G (partD.right l) i) i)
    (radius (fun i j => pZ.GI (partI.right j) i) i)
  refine le_trans (abs_add_le _ _) ?_
  simp only [PolyZonotope.dropRadius]
  linarith


omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduceBy`'s independent generator count, stated
through the projection because that is the form the goal has and simp will not
rewrite a binder's type. -/
private theorem PolyZonotope.aux_sum_univ_reduceBy_q {pZ : PolyZonotope (Vec 𝕋 n)}
    {partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)} (f : Fin (dI + n) → ℝ) :
    ∑ j : Fin (pZ.reduceBy partD partI).q, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd dI j) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The dependent count needs no splitting, only its binder read back at `d`:
`ring` treats a sum over `Fin (pZ.reduceBy partD partI).h` and one over `Fin d`
as two atoms, defeq or not. -/
private theorem PolyZonotope.aux_sum_univ_reduceBy_h {pZ : PolyZonotope (Vec 𝕋 n)}
    {partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)}
    {partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)} (f : Fin d → ℝ) :
    ∑ l : Fin (pZ.reduceBy partD partI).h, f l = ∑ l, f l :=
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `pZ` at the factors `a` and the independent coefficients `β` is a point of the
reduced set at the same `a`: the dropped columns become one diagonal block, at the coefficient
`aux_abs_dropped_le_dropRadius` says reaches them, and the kept columns are the original ones. -/
theorem PolyZonotope.reduceBy_point (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {a : Fin pZ.p → ℝ}
    {β : Fin pZ.q → ℝ} (ha : ∀ k, |a k| ≤ 1) (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ∃ β' : Fin (pZ.reduceBy partD partI).q → ℝ, (∀ j, |β' j| ≤ 1) ∧ ∀ i,
      toReal (pZ.c i) + (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
          + ∑ j, toReal (pZ.GI j i) * β j
        = toReal ((pZ.reduceBy partD partI).c i)
          + (∑ l, toReal ((pZ.reduceBy partD partI).G l i)
              * Real.PolyZonotope.monomial (pZ.reduceBy partD partI).E a l)
          + ∑ j, toReal ((pZ.reduceBy partD partI).GI j i) * β' j := by -- --- PROOF ---
  have hbound := PolyZonotope.aux_abs_dropped_le_dropRadius pZ partD partI ha hβ
  refine ⟨Fin.append (fun j => β (partI.left j)) (fun i => Real.Zonotope.coefficient
        (toReal (pZ.dropRadius partD partI i))
        ((∑ l, toReal (pZ.G (partD.right l) i)
            * Real.PolyZonotope.monomial pZ.E a (partD.right l))
          + ∑ j, toReal (pZ.GI (partI.right j) i) * β (partI.right j))), ?_, fun i => ?_⟩
  -- the kept coefficients are unchanged; the fresh ones are scaled to that box
  · refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa using hβ (partI.left j)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound i)) (hbound i)
  · rw [partD.sum_split₂ fun l => toReal (pZ.G l i)
        * Real.PolyZonotope.monomial pZ.E a l,
      partI.sum_split₂ fun j => toReal (pZ.GI j i) * β j,
      PolyZonotope.aux_sum_univ_reduceBy_q, PolyZonotope.aux_sum_univ_reduceBy_h]
    simp only [PolyZonotope.reduceBy, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]
    -- the kept columns are the original ones, so their monomials are too
    have hmono : ∀ l : Fin d,
        Real.PolyZonotope.monomial (fun k l => pZ.E k (partD.left l)) a l
          = Real.PolyZonotope.monomial pZ.E a (partD.left l) := fun _ => rfl
    simp only [hmono]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
