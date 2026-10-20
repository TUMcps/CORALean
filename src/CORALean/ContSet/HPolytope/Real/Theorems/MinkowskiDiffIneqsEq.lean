module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The Minkowski difference of an H-polytope, exactly

[1, Eq. 27]: `⟨A₁, b₁⟩ ⊖ S = ⟨A₁, b*⟩` with `b*(j) = b₁(j) - ρ(S, A₁(j,·))`, for any subtrahend
`S`, as the paper notes. Offsets are extended reals: an empty `S` (`ρ = -∞`) drops every row and
gives `ℝⁿ`, an `S` unbounded along a row (`ρ = +∞`) gives `∅`. `HPolytope.minkDiffOf_inner` is
the version with real bounds in place of `ρ`, inner only.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `S` – set of points

## Hypotheses
* none

## Conclusion
* the Minkowski difference of an H-polytope, exactly

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real number below `b - ρ` in the extended reals: `ρ` below `b - a`, read on the reals. -/
theorem aux_coe_le_sub_iff (a b : ℝ) (ρ : EReal) :
    (a : EReal) ≤ (b : EReal) - ρ ↔ ρ ≤ ((b - a : ℝ) : EReal) := by -- --- PROOF ---
  induction ρ using EReal.rec with
  | bot => simp
  | top =>
    simp only [top_le_iff, EReal.coe_ne_top, iff_false]
    simp
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkowskiDiff_ineqs_eq (A : Mat ℝ q n) (b : Vec ℝ q) (S : Set (Vec ℝ n)) :
    minkowskiDiff (HPolytope.ineqs A b).construct S =
      {x | ∀ j, (((A *ᵥ x) j : ℝ) : EReal) ≤
        (b j : EReal) - supportFunc S (HPolytope.rowLin A j)} := by -- --- PROOF ---
  ext x
  simp only [minkowskiDiff, Set.mem_setOf_eq, aux_coe_le_sub_iff, supportFunc_le_coe_iff]
  constructor
  · intro h j y hy
    have := HPolytope.mem_ineqs_iff.mp (h y hy) j
    rw [Matrix.mulVec_add, Pi.add_apply] at this
    show (A *ᵥ y) j ≤ b j - (A *ᵥ x) j
    linarith
  · intro h y hy
    refine HPolytope.mem_ineqs_iff.mpr fun j => ?_
    have : (A *ᵥ y) j ≤ b j - (A *ᵥ x) j := h j y hy
    rw [Matrix.mulVec_add, Pi.add_apply]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
