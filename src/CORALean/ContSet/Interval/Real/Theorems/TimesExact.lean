import CORALean.ContSet.Interval.Real.Theorems.TimesOuter
import CORALean.ContSet.Interval.Real.Theorems.ExistsMulEq
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

/-!
# `Interval.times` is exactly the set of entrywise products of nonempty boxes

`times_outer` is the inclusion; the other direction picks each coordinate's factors by
`exists_mul_eq`. Needs both boxes nonempty: with a crossed coordinate the corner hull is an
interval nobody multiplies into.

[1, Eq. 2]: the product is the hull of the four corner products, exactly.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.times_exact {I J : Interval (Vec ℝ n)} (hI : I.IsNonempty) (hJ : J.IsNonempty) :
    (I.times J).construct =
      Set.image2 (fun x y i => x i * y i) I.construct J.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm (fun z hz => ?_) (Interval.times_outer I J)
  have h : ∀ i, ∃ y x, (I.inf i ≤ y ∧ y ≤ I.sup i) ∧ (J.inf i ≤ x ∧ x ≤ J.sup i) ∧
      y * x = z i :=
    fun i => Interval.exists_mul_eq (hI i) (hJ i) (hz i).1 (hz i).2
  choose y x hy hx hyx using h
  exact ⟨y, fun i => hy i, x, fun i => hx i, funext hyx⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
