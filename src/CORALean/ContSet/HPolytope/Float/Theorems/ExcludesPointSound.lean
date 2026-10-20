module

public import CORALean.ContSet.HPolytope.Float.Operations.ExcludesPoint
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct

@[expose] public section

/-!
# `HPolytope.excludesPoint` proves the point outside

The rounded dot product is on the far side of the exact one (`dotDown_le`, `le_dotUp`), and
`ltStrict`'s `true` is a strict real inequality, so the violated row holds for the exact point.

## Inputs
* `P` – H-polytope
* `x` – point of length `n`

## Hypotheses
* `h` – `P.excludesPoint x` holds

## Conclusion
* `HPolytope.excludesPoint` proves the point outside
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.excludesPoint_sound (P : HPolytope 𝕋 (Vec 𝕋 n)) (x : Vec 𝕋 n)
    (h : P.excludesPoint x = true) : -- --- CONCL ---
    toRealVec x ∉ P.construct := by -- --- PROOF ---
  intro hx
  obtain ⟨hA, hAe⟩ := HPolytope.rows_of_mem_construct hx
  -- a row of the stored matrix at the stored point, read exactly
  have hrow : ∀ {k : ℕ} (M : Mat 𝕋 k n) (i : Fin k),
      (toRealMat M *ᵥ toRealVec x) i = ∑ j, toReal (M i j) * toReal (x j) := fun M i => by
    simp [Matrix.mulVec, dotProduct, toRealMat, toRealVec]
  unfold HPolytope.excludesPoint at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and] at h
  rcases h with ⟨i, hi⟩ | ⟨i, hi | hi⟩
  · -- an inequality, violated
    have h1 := toReal_lt_of_ltStrict hi
    have h2 := dotDown_le (P.A i) x
    have h3 := hA i
    rw [hrow] at h3
    linarith
  · -- an equality row, above its upper bound
    have h1 := toReal_lt_of_ltStrict hi
    have h2 := dotDown_le (P.Ae i) x
    have h3 := (hAe i).1
    rw [hrow] at h3
    linarith
  · -- an equality row, below its lower bound
    have h1 := toReal_lt_of_ltStrict hi
    have h2 := dotDown_le (-(P.Ae i)) x
    have h3 := (hAe i).2
    rw [hrow] at h3
    simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib] at h2
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
