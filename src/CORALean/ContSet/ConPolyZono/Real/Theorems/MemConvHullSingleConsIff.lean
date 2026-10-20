module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCartProdIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCopiesIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemLinearIff
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# What the convex hull's constraint says

Every copy's equations, each at its own block of factors, and the weights summing to `1 - a`
(the weights are `λⱼ - 1` there, [1, Prop. 9]'s shift): `PolyLevelSet.mem_cartProd_iff` splits
the copies from the weight row, `mem_copies_iff` the copies from one another, and
`mem_linear_iff` reads the weight row.

## Inputs
* `a` – number of weights
* `cPZ` – constrained polynomial zonotope
* `v` – factor values

## Hypotheses
* none

## Conclusion
* the hull constraint holds exactly when each copy and the weights are valid

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull's equations hold exactly when every copy's do and the weight factors lie in the unit
box and add up to what a convex combination needs. -/
theorem ConPolyZono.mem_convHullSingle_cons_iff (a : ℕ) (cPZ : ConPolyZono α)
    (v : Fin (a * cPZ.p + a) → ℝ) : -- --- CONCL ---
    v ∈ (cPZ.convHullSingle a).cons.construct
      ↔ (∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ cPZ.cons.construct)
        ∧ (∀ j, |v (Fin.natAdd (a * cPZ.p) j)| ≤ 1)
        ∧ ∑ j, v (Fin.natAdd (a * cPZ.p) j) = 1 - (a : ℝ) := by -- --- PROOF ---
  show v ∈ ((cPZ.cons.copies a).cartProd _).construct ↔ _
  rw [PolyLevelSet.mem_cartProd_iff, PolyLevelSet.mem_copies_iff, PolyLevelSet.mem_linear_iff,
    Interval.mem_unit_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h _ => ?_⟩)
  · have h0 := h 0
    simp only [CompOp.holds, Pi.sub_apply, Matrix.mulVec, dotProduct, one_mul, sub_eq_zero] at h0
    exact h0
  · simp only [CompOp.holds, Pi.sub_apply, Matrix.mulVec, dotProduct, one_mul, sub_eq_zero]
    exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
