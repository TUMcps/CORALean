module

public import CORALean.ContSet.HPolytope.Real.Theorems.EqZeroOfMulVecNonpos
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# A bounded nonempty H-polytope needs `n + 1` halfspaces

[1, Sec. 4.2 fn. 3]: no bounded, non-degenerate H-polytope in `ℝⁿ` has fewer than `n + 1`
halfspaces, the simplex's count. Nonempty suffices: with `q ≤ n` rows some `d ≠ 0` has `A d ≤ 0`
— `A d = -1` if `-1` is in the range of `A`, a kernel vector otherwise, the range then being too
small — and that recession direction makes the polytope unbounded. `n ≥ 1`, the paper's `ℝⁿ`:
`ℝ⁰` is bounded and full with no halfspace at all.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`

## Hypotheses
* `hn` – `0 < n`
* `hne` – the polytope `ineqs A b` is nonempty
* `hb` – `(HPolytope.ineqs A b)` is bounded

## Conclusion
* A bounded nonempty H-polytope needs `n + 1` halfspaces

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
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

/-- With at most `n` rows, some nonzero direction no row increases along. -/
theorem aux_exists_ne_zero_mulVec_nonpos (A : Mat ℝ q n) (hn : 0 < n)
    (hq : q ≤ n) : -- --- CONCL ---
    ∃ d : Vec ℝ n, d ≠ 0 ∧ A *ᵥ d ≤ 0 := by -- --- PROOF ---
  by_cases hs : ∃ d : Vec ℝ n, A *ᵥ d = -1
  · obtain ⟨d, hd⟩ := hs
    by_cases hd0 : d = 0
    -- `A 0 = -1` leaves no row at all, so any nonzero direction will do
    · have hq0 : q = 0 := by
        by_contra hq0
        have := congrFun hd ⟨0, Nat.pos_of_ne_zero hq0⟩
        rw [hd0, Matrix.mulVec_zero] at this
        norm_num at this
      subst hq0
      refine ⟨Pi.single ⟨0, hn⟩ 1, fun h => ?_, fun i => i.elim0⟩
      have := congrFun h ⟨0, hn⟩
      simp at this
    · exact ⟨d, hd0, fun i => by rw [hd]; norm_num⟩
  -- `-1` outside the range: the range is a proper subspace, so the kernel is not trivial
  · have hne : LinearMap.range (Matrix.mulVecLin A) ≠ ⊤ := fun htop =>
      hs (by
        obtain ⟨d, hd⟩ := LinearMap.range_eq_top.mp htop (-1)
        exact ⟨d, hd⟩)
    have hlt := Submodule.finrank_lt hne
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
    rw [Module.finrank_fin_fun] at hlt hrk
    have hker : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ := fun hbot => by
      rw [hbot, finrank_bot] at hrk
      omega
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    refine ⟨d, hd0, fun i => ?_⟩
    have : A *ᵥ d = 0 := hd
    rw [this]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.succ_le_of_isBounded {A : Mat ℝ q n} {b : Vec ℝ q} (hn : 0 < n)
    (hne : (HPolytope.ineqs A b).construct.Nonempty)
    (hb : Bornology.IsBounded (HPolytope.ineqs A b).construct) : n + 1 ≤ q := by
  by_contra hq
  obtain ⟨d, hd0, hd⟩ := aux_exists_ne_zero_mulVec_nonpos A hn (by omega)
  exact hd0 (HPolytope.eq_zero_of_mulVec_nonpos hne hb hd)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
