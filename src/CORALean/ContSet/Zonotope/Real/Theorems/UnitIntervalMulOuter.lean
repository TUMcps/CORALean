module

public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

/-!
# `[-1, 1] ⊗ Z` is enclosed by `(0, c, g⁽¹⁾, ..., g⁽ᵖ⁾)`

[1, Eq. 11]: `s(c + Σⱼ βⱼg⁽ʲ⁾) = 0 + s·c + Σⱼ (sβⱼ)g⁽ʲ⁾`, and `|s| ≤ 1`, `|βⱼ| ≤ 1` put
every coefficient back in `[-1, 1]`.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* all products with the unit interval lie in the result

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 11]: `[-1, 1] ⊗ Z ⊆ (0, c, g⁽¹⁾, ..., g⁽ᵖ⁾)`. -/
theorem Zonotope.unitIntervalMul_outer (Z : Zonotope α) : -- --- CONCL ---
    (fun sx : ℝ × α => sx.1 • sx.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ Z.construct)
      ⊆ Z.unitIntervalMul.construct := by -- --- PROOF ---
  rintro _ ⟨⟨s, x⟩, ⟨hs, β, hβ, rfl⟩, rfl⟩
  have hs' : |s| ≤ 1 := abs_le.mpr hs
  -- the center's coefficient is `s`, generator `j`'s is `s βⱼ`
  have hγ : ∀ k, |(Fin.cons s fun j => s * β j : Fin (Z.h + 1) → ℝ) k| ≤ 1 := by
    refine Fin.cases hs' fun j => ?_
    rw [Fin.cons_succ, abs_mul]
    exact mul_le_one₀ hs' (abs_nonneg _) (hβ j)
  refine ⟨_, hγ, ?_⟩
  show s • (Z.c + ∑ j, β j • Z.G j) = 0 + ∑ k, (Fin.cons s fun j => s * β j : Fin (Z.h + 1) → ℝ) k
      • (Fin.cons Z.c Z.G : Fin (Z.h + 1) → α) k
  rw [Fin.sum_univ_succ, smul_add, Finset.smul_sum, zero_add]
  simp only [Fin.cons_zero, Fin.cons_succ, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
