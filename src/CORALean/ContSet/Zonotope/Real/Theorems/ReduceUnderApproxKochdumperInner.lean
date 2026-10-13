module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxKochdumper
public import CORALean.ContSet.Zonotope.Real.Theorems.MulGensInner
public import CORALean.ContSet.Zonotope.Real.Theorems.SortByLengthConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.SumAbsLeOneOfSubsingletonSupport

@[expose] public section

/-!
# `reduceUnderApproxKochdumper` returns a subset

The reduced generators are `G_s T` with `T` having one entry per row, `1` for a kept
generator and `±1` for a summed one, so `‖T‖∞ ≤ 1` and [1, Eq. (1)] puts the result in `Z`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. III-C]: the reduced zonotope is inside `Z`. -/
theorem Zonotope.reduceUnderApproxKochdumper_inner [NeZero n] (Z : Zonotope (Vec ℝ n)) (r : ℕ)
    (hr : r ≤ Z.h) :
    (Z.reduceUnderApproxKochdumper r hr).construct ⊆ Z.construct := by -- --- PROOF ---
  rw [← Zonotope.sortByLength_construct Z]
  -- the result is `G_s T` for `T` with a `1` per kept generator and a sign per summed one
  let T : Mat ℝ Z.sortByLength.h r := fun j i =>
    if (i : ℕ) + 1 < r then (if (j : ℕ) = i then 1 else 0)
    else if r ≤ (j : ℕ) + 1 then (if Z.sortByLength.G j 0 < 0 then -1 else 1) else 0
  have hG : Z.reduceUnderApproxKochdumper r hr = Z.sortByLength.mulGens T := by
    simp only [Zonotope.reduceUnderApproxKochdumper, Zonotope.mulGens]
    congr 1
    funext i
    by_cases h : (i : ℕ) + 1 < r
    · -- a kept generator: only its own row contributes
      rw [if_pos h, Finset.sum_eq_single (show Fin Z.sortByLength.h from i.castLE hr)]
      · simp [T, h]
      · intro j _ hj
        have : (j : ℕ) ≠ i := fun e => hj (Fin.ext e)
        simp [T, h, this]
      · simp
    · -- the summed generators, signed
      rw [if_neg h, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [T, h]
  rw [hG]
  refine Zonotope.mulGens_inner _ _ fun j => ?_
  refine Zonotope.sum_abs_le_one_of_subsingleton_support _ (fun i i' hi hi' => ?_) (fun i => ?_)
  · -- a nonzero entry is in a kept column of its own row, or in the last column
    have ex : ∀ i : Fin r, T j i ≠ 0 →
        (((i : ℕ) + 1 < r ∧ (j : ℕ) = i) ∨ (¬ (i : ℕ) + 1 < r ∧ r ≤ (j : ℕ) + 1)) := by
      intro i hi
      by_cases h1 : (i : ℕ) + 1 < r
      · by_cases h2 : (j : ℕ) = i
        · exact Or.inl ⟨h1, h2⟩
        · simp [T, h1, h2] at hi
      · by_cases h3 : r ≤ (j : ℕ) + 1
        · exact Or.inr ⟨h1, h3⟩
        · simp [T, h1, h3] at hi
    have := i.isLt
    have := i'.isLt
    rcases ex i hi with h | h <;> rcases ex i' hi' with h' | h' <;> exact Fin.ext (by omega)
  · -- every entry is `0` or `±1`
    simp only [T]
    split_ifs <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
