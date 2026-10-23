module

public import CORALean.ContSet.Zonotope.Real.Theorems.NegSumAbsLeSumMul
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A zonotope misses a polytope beyond one of its halfspaces

[1, Eq. 8], the set-based verification of [1, Alg. 1]: for `Y = ⟨c_y, G_y⟩_Z` and
`U = ⟨A, b⟩_H`, if `A(i,·) c_y - |A(i,·) G_y| 1 > b(i)` for some row `i`, then `Y ∩ U = ∅`, since
`A(i,·) c_y - |A(i,·) G_y| 1` is the least value of `A(i,·) y` over `Y`. Only the sufficient
direction is printed, and it is all the verification needs.

## Inputs
* `Y` – output zonotope
* `A` – unsafe-set matrix
* `b` – unsafe-set offset

## Hypotheses
* `h` – some row's least value over `Y` exceeds its offset

## Conclusion
* `Y ∩ U = ∅`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 8]: a row whose least value over `Y` exceeds its offset separates `Y` from `U`. -/
theorem Zonotope.inter_ineqs_eq_empty_of_row (Y : Zonotope (Vec ℝ k)) (A : Mat ℝ p k)
    (b : Vec ℝ p) (h : ∃ i, b i < (A *ᵥ Y.c) i - ∑ j, |(A *ᵥ Y.G j) i|) : -- --- CONCL ---
    Y.construct ∩ (HPolytope.ineqs A b).construct = ∅ := by -- --- PROOF ---
  obtain ⟨i, hi⟩ := h
  refine Set.eq_empty_iff_forall_notMem.2 fun y ⟨⟨β, hβ, hy⟩, hU⟩ => ?_
  have hUi := (HPolytope.mem_ineqs_iff).1 hU i
  rw [hy, mulVec_add, mulVec_sum, Pi.add_apply, Finset.sum_apply] at hUi
  simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul] at hUi
  -- the least value of row `i` over `Y` is `A(i,·) c_y - |A(i,·) G_y| 1`
  have hlow := Zonotope.neg_sum_abs_le_sum_mul Finset.univ β (fun j => (A *ᵥ Y.G j) i) hβ
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
