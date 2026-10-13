import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByCoeff

/-!
# Lifting, reducing and reading the rows back over-approximates, in floats

[1, Sec. 4.3] on the stored floats.

A point `y + e` of `cZ`, `y` nominal at `β`: `Zonotope.reduceBy_coeff` on the lifted zonotope
gives coefficients `ξ` that agree with `β` on the kept generators and reproduce every
coordinate of the lifted sum. The upper coordinates are `y`, so the point is the result's
nominal point at `ξ` plus the same `e`. The lower coordinates are `Aₑ β`, which the new
equality rows read at `ξ` as the same number, inside the unchanged interval `bₑ`. An
inequality row at `ξ` is the row at `β` on the kept generators, which is the full row less
what the dropped ones contribute, at most their reach, and `radius` rounded up covers it.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLiftBy_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) :
    cZ.construct ⊆ (cZ.reduceLiftBy part).construct := by -- --- PROOF ---
  rintro x ⟨y, hy', e, he, hx⟩
  obtain ⟨β, hβ, hP, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  obtain ⟨hPin, hPeq⟩ := HPolytope.mem_construct_iff.mp hP
  obtain ⟨ξ, hξ, hξl, hsum⟩ := Zonotope.reduceBy_coeff cZ.liftEq part β hβ
  refine ⟨y, ConZonotope.mem_nominalSet_iff.mpr ⟨ξ, hξ, ?_, fun k => ?_⟩, e, he, hx⟩
  · refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · -- the row at the kept coefficients, against the full row and the dropped reach
      have hfull := hPin i
      simp only [mulVec, dotProduct, toRealMat] at hfull ⊢
      rw [part.sum_split₂ fun j => toReal (cZ.P.A i j) * β j] at hfull
      have hdrop : -toReal (radius (fun i l => cZ.P.A i (part.right l)) i)
          ≤ ∑ l, toReal (cZ.P.A i (part.right l)) * β (part.right l) := by
        have h1 : ∑ l, |toReal (cZ.P.A i (part.right l))|
            ≤ toReal (radius (fun i l => cZ.P.A i (part.right l)) i) :=
          sum_abs_le_radius (d := fun i l => cZ.P.A i (part.right l)) i
        have h2 : -∑ l, |toReal (cZ.P.A i (part.right l))|
            ≤ ∑ l, toReal (cZ.P.A i (part.right l)) * β (part.right l) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_le_sum fun l _ => ?_
          have := abs_le.mp (show |toReal (cZ.P.A i (part.right l)) * β (part.right l)|
              ≤ |toReal (cZ.P.A i (part.right l))| by
            rw [abs_mul]
            simpa using mul_le_mul_of_nonneg_left (hβ (part.right l)) (abs_nonneg _))
          linarith [this.1]
        linarith
      -- the row of the result at `ξ`: kept coefficients only
      have hrow : ∑ j : Fin (q + (n + cZ.P.me)),
          toReal ((cZ.reduceLiftBy part).P.A i j) * ξ j
          = ∑ l, toReal (cZ.P.A i (part.left l)) * β (part.left l) := by
        rw [Fin.sum_univ_add]
        simp only [ConZonotope.reduceLiftBy, Fin.append_left, Fin.append_right, toReal_zero,
          zero_mul, Finset.sum_const_zero, add_zero, hξl]
        rfl
      refine le_trans (le_of_eq hrow) ?_
      refine le_trans ?_ (add_le_addUp (cZ.P.b i)
        (radius (fun i l => cZ.P.A i (part.right l)) i))
      linarith
    · -- the lower coordinates of the lifted sum are the original equality rows
      have heq := hPeq i
      simp only [mulVec, dotProduct, toRealMat] at heq ⊢
      have hs := hsum (Fin.natAdd n i)
      simp only [ConZonotope.liftEq, Fin.append_right] at hs
      have key : ∑ j : Fin (cZ.reduceLiftBy part).h,
          toReal ((cZ.reduceLiftBy part).P.Ae i j) * ξ j
          = ∑ j, toReal (cZ.P.Ae i j) * β j := by
        exact hs.symm
      rw [key]
      exact heq
  · -- the upper coordinates are the point itself
    have hs := hsum (Fin.castAdd cZ.P.me k)
    simp only [ConZonotope.liftEq, Fin.append_left] at hs
    rw [hy k]
    exact congrArg (toReal (cZ.c k) + ·) hs

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
