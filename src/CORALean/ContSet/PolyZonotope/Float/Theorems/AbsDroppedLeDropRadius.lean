module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

@[expose] public section

/-!
# One box covers what both dropped blocks of `reduceBy` contribute

`abs_sum_le_radius` takes either block's coefficients, needing only
`|coefficient| ≤ 1` — a monomial for the dependent one, free for the
independent one — so their two radii, added upward, bound the sum.

## Inputs
* `pZ` – polynomial zonotope
* `partD` – split of the dependent generators
* `partI` – split of the independent generators
* `a` – factor values
* `β` – independent factor values
* `i` – coordinate

## Hypotheses
* `ha` – factor values are at most one
* `hβ` – independent factor values are at most one

## Conclusion
* the dropped part is bounded by the drop radius
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the dropped dependent generators contribute, so what the block must
cover. The coefficients are monomials, and `abs_sum_le_radius` asks only that
they lie in `[-1, 1]`. -/
theorem PolyZonotope.aux_abs_droppedDep_le (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r)) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |∑ l, toReal (pZ.G (partD.right l) i)
        * Real.PolyZonotope.monomial pZ.E a (partD.right l)|
      ≤ toReal (radius (fun i l => pZ.G (partD.right l) i) i) :=
  abs_sum_le_radius (d := fun i l => pZ.G (partD.right l) i) (fun _ _ => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one pZ.E ha (partD.right l)) i

/-- The same for the dropped independent generators, whose coefficients are
free to begin with. -/
theorem PolyZonotope.aux_abs_droppedInd_le (pZ : PolyZonotope (Vec 𝕋 n))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {β : Fin pZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |∑ j, toReal (pZ.GI (partI.right j) i) * β (partI.right j)|
      ≤ toReal (radius (fun i j => pZ.GI (partI.right j) i) i) :=
  abs_sum_le_radius (d := fun i j => pZ.GI (partI.right j) i) (fun _ _ => le_refl _)
    (fun j => hβ (partI.right j)) i


-- =======================================  MAIN THEOREM  ======================================= --

/-- One box for the two dropped blocks: their radii, added upward. -/
theorem PolyZonotope.abs_dropped_le_dropRadius (pZ : PolyZonotope (Vec 𝕋 n))
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
