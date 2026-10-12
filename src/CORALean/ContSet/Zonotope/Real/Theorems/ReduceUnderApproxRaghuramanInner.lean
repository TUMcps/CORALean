import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxRaghuraman
import CORALean.ContSet.Zonotope.Real.Theorems.MulGensInner
import CORALean.ContSet.Zonotope.Real.Theorems.SortByLengthConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.SumAbsLeOneOfSubsingletonSupport

/-!
# `reduceUnderApproxRaghuraman` returns a subset

Each row of the printed `T` has at most one nonzero entry, of modulus at most `1`: a
large generator keeps itself, a small one goes to the one it is strictly most aligned
with. So `‖T‖∞ ≤ 1` and [1, Eq. (1)] puts the reduced zonotope inside `Z`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. III-B]: the reduced zonotope is inside `Z`. -/
theorem Zonotope.reduceUnderApproxRaghuraman_inner (Z : Zonotope (Vec ℝ n)) (r : ℕ)
    (hr : r ≤ Z.h) :
    (Z.reduceUnderApproxRaghuraman r hr).construct ⊆ Z.construct := by -- --- PROOF ---
  -- the result is `Z_s T`, and `Z_s` is `Z` with its generators permuted
  rw [← Zonotope.sortByLength_construct Z]
  refine Zonotope.mulGens_inner _ _ fun j => ?_
  -- the printed `P`, so that the two cases of an entry can be named
  let P : Fin Z.sortByLength.h → Fin Z.sortByLength.h → ℝ :=
    fun j i => Z.sortByLength.G i ⬝ᵥ Z.sortByLength.G j
  have key : ∀ i : Fin r, (if (j : ℕ) = i then (1 : ℝ)
      else if r ≤ j ∧ ∀ k : Fin r, k ≠ i → |P j (k.castLE hr)| < |P j (i.castLE hr)|
        then P j (i.castLE hr) / |P j (i.castLE hr)| else 0) ≠ 0 →
      (j : ℕ) = i ∨ (r ≤ j ∧ ∀ k : Fin r, k ≠ i → |P j (k.castLE hr)| < |P j (i.castLE hr)|) := by
    intro i hi
    by_cases h1 : (j : ℕ) = i
    · exact Or.inl h1
    · rw [if_neg h1] at hi
      by_cases h2 : r ≤ j ∧ ∀ k : Fin r, k ≠ i → |P j (k.castLE hr)| < |P j (i.castLE hr)|
      · exact Or.inr h2
      · rw [if_neg h2] at hi
        exact absurd rfl hi
  refine Zonotope.sum_abs_le_one_of_subsingleton_support _ (fun i i' hi hi' => ?_) (fun i => ?_)
  · -- at most one nonzero entry
    rcases key i hi with h1 | h2 <;> rcases key i' hi' with h1' | h2'
    · exact Fin.ext (h1.symm.trans h1')
    · exact absurd (h2'.1) (by have := i'.isLt; omega)
    · exact absurd (h2.1) (by have := i.isLt; omega)
    · -- the strict maximum is unique
      by_contra hne
      have a := h2.2 i' (Ne.symm hne)
      have b := h2'.2 i hne
      linarith
  · -- `1`, or `P/|P|`, or `0`
    show |if (j : ℕ) = i then (1 : ℝ) else _| ≤ 1
    split_ifs
    · simp
    · rw [abs_div, abs_abs]; exact div_self_le_one _
    · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
