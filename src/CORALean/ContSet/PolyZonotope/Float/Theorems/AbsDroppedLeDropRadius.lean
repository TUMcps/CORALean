import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# One box covers what both dropped blocks of `reduceBy` contribute

`abs_sum_le_radius` takes either block's coefficients, needing only
`|coefficient| ≤ 1` — a monomial for the dependent one, free for the
independent one — so their two radii, added upward, bound the sum.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}

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

end CORALean.Float
