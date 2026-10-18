module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxNLP
public import CORALean.ContSet.Zonotope.Real.Theorems.MulGensInner
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitKeptAddSplitDroppedSubset

@[expose] public section

/-!
# `reduceUnderApproxNLP` returns a subset

If the program (6) returns `Ĝ_b = G_b T` with `‖T‖∞ ≤ 1` ([1, Eq. (1)]), then `⟨0, Ĝ_b⟩ ⊆ ⟨0, G_b⟩`
and so `⟨c, G_a⟩ ⊕ ⟨0, Ĝ_b⟩ ⊆ ⟨c, G_a⟩ ⊕ ⟨0, G_b⟩ = Z`. Nothing is said of volume: the theorem does
not say that `Ĝ_b` is optimal.

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
open scoped CORALean
open Pointwise
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-D]: for a `Ĝ_b` meeting (1) against `G_b`, the reduced zonotope is inside `Z`. -/
theorem Zonotope.reduceUnderApproxNLP_inner (Z : Zonotope (Vec ℝ n)) (r : ℕ) (hn : n ≤ r)
    (hr : r < Z.h) (Gb' : Fin n → Vec ℝ n)
    (T : Mat ℝ (Z.splitDropped (Z.lengthSplit (r - n) (by omega))).h n)
    (hG : ∀ k, Gb' k = ∑ i, T i k • (Z.splitDropped (Z.lengthSplit (r - n) (by omega))).G i)
    (hT : ∀ i, ∑ k, |T i k| ≤ 1) : -- --- STMT ---
    (Z.reduceUnderApproxNLP r hn hr Gb').construct ⊆ Z.construct := by -- --- PROOF ---
  -- `⟨0, Ĝ_b⟩ = ⟨0, G_b T⟩` is inside `⟨0, G_b⟩` by (1)
  have hb : (⟨n, 0, Gb'⟩ : Zonotope (Vec ℝ n)).construct ⊆
      (Z.splitDropped (Z.lengthSplit (r - n) (by omega))).construct := by
    have h := Zonotope.mulGens_inner (Z.splitDropped (Z.lengthSplit (r - n) (by omega))) T hT
    have e : (Z.splitDropped (Z.lengthSplit (r - n) (by omega))).mulGens T = ⟨n, 0, Gb'⟩ := by
      simp only [Zonotope.mulGens, Zonotope.splitDropped]
      congr 1
      funext k
      exact (hG k).symm
    rwa [e] at h
  -- `Z_a ⊕ ⟨0, Ĝ_b⟩ ⊆ Z_a ⊕ Z_b ⊆ Z`
  unfold Zonotope.reduceUnderApproxNLP
  simp only []
  rw [← Zonotope.plus_exact]
  exact (Set.add_subset_add_left hb).trans
    (Zonotope.splitKept_add_splitDropped_subset Z _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
