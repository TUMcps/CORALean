module

public import CORALean.ContSet.Zonotope.Real.Operations.Inclusion
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Definitions.Coefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.inclusion` encloses the interval family

[1, Prop. 4], that is [2, Thm. 4]: for every `M ∈ [M]` and `b ∈ Bᵐ`, `p + M b = p + mid[M] b + (M -
mid[M]) b`, and coordinate `i` of the last term is at most `Σⱼ rad[M]ᵢⱼ` in size, which the `i`-th
axis generator reaches. Outer only, as the paper states it.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.inclusion_outer (p : Vec ℝ n) (IM : Interval (Mat ℝ n m)) :
    (⋃ M ∈ IM.construct, {x | ∃ b : Vec ℝ m, (∀ j, |b j| ≤ 1) ∧ x = p + M *ᵥ b})
      ⊆ (Zonotope.inclusion p IM).construct := by -- --- PROOF ---
  rintro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨M, hM, b, hb, rfl⟩ := hx
  have hrad : ∀ i j, 0 ≤ IM.radius i j :=
    fun i j => (abs_nonneg _).trans (IM.abs_sub_center_le hM (i, j))
  -- what `M - mid[M]` adds to coordinate `i`, at most the row's radius sum
  set err : Fin n → ℝ := fun i => ∑ j, (M i j - IM.center i j) * b j with herr
  have herrb : ∀ i, |err i| ≤ ∑ j, IM.radius i j := by
    intro i
    calc |err i|
        ≤ ∑ j, |(M i j - IM.center i j) * b j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M i j - IM.center i j| * |b j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, IM.radius i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul (IM.abs_sub_center_le hM (i, j)) (hb j) (abs_nonneg _) (hrad i j)
      _ = ∑ j, IM.radius i j := by simp
  have hrsnn : ∀ i, 0 ≤ ∑ j, IM.radius i j := fun i => (abs_nonneg _).trans (herrb i)
  -- the witness: `b` on the centre's columns, the scaled spread on the axis generators
  refine Zonotope.mem_construct_iff.mpr
    ⟨Fin.append b (fun i => Zonotope.coefficient (∑ j, IM.radius i j) (err i)), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hb l
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hrsnn i) (herrb i)
  · show _ = p i + ∑ x : Fin (m + n), _
    rw [Fin.sum_univ_add]
    simp only [Zonotope.inclusion, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (herrb i)]
    simp only [herr, Pi.add_apply, Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
