import CORALean.ContSet.Zonotope.Real.Operations.RaghuramanAlphaMaxCora

/-!
# CORA's `'raghuraman'` reduction divides `0/0` on a valid zonotope

In `@zonotope/reduceUnderApprox.m`, `aux_reduceUnderApproxRaghuraman` (lines 260-281) sets
`T(k, idx) = G_prod(k, idx)./alpha_max'` (lines 275-276) with `alpha_max` the largest `|G_prod|` of
the `k`-th small generator against the kept ones. If that generator is orthogonal to all of them,
both numerator and `alpha_max` are `0`, the entry is `NaN`, and the `zonotope` constructor (with
`CHECKS_ENABLED`, `'nonnan'`) throws: no reduction is returned for a zonotope with finite
generators. Here `⟨0, [(3,0), (2,0), (0,1)]⟩` with `eta_new = 2` (`order = 1`, `n = 2`, so
`n·order < 3` and the reduction runs). Also, line 280 multiplies the unsorted `generators(Z)` by
the `T` built for the sorted ones; since every row of `T` has `‖·‖₁ ≤ 1` the result stays inside
`Z`, but it is not the paper's reduction. Only the `0/0` is stated.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.raghuramanCora_zeroDivision :
    let Z : Zonotope (Vec ℝ 2) := ⟨3, 0, ![![3, 0], ![2, 0], ![0, 1]]⟩
    ∃ hr : 2 ≤ Z.h, (∀ i, Z.raghuramanGProdCora 2 hr ⟨0, by norm_num [Z]⟩ i = 0) ∧
      Z.raghuramanAlphaMaxCora 2 hr ⟨0, by norm_num [Z]⟩ = 0 := by -- --- PROOF ---
  intro Z
  -- the generators are already sorted by length, so `sortByLength` changes nothing
  have hsort : Tuple.sort (fun j => -Z.generatorLength j) = Equiv.refl _ := by
    rw [Tuple.sort_eq_refl_iff_monotone]
    -- the generator lengths are `3`, `2`, `1`
    have h3 : Z.generatorLength 0 = 3 := by
      simp [Zonotope.generatorLength, Z, norm₂, Fin.sum_univ_succ]
    have h2 : Z.generatorLength 1 = 2 := by
      simp [Zonotope.generatorLength, Z, norm₂, Fin.sum_univ_succ]
    have h1 : Z.generatorLength 2 = 1 := by
      simp [Zonotope.generatorLength, Z, norm₂, Fin.sum_univ_succ]
    -- the lengths are `3 - a`, so the negated lengths are monotone
    show Monotone (fun j : Fin 3 => -Z.generatorLength j)
    have hl : ∀ a : Fin 3, Z.generatorLength a = 3 - (a : ℕ) := by
      intro a
      fin_cases a
      · simpa using h3
      · show Z.generatorLength 1 = _
        rw [h2]; norm_num
      · show Z.generatorLength 2 = _
        rw [h1]; norm_num
    intro a b hab
    -- compare the lengths through `hl`
    have hab' : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    show -Z.generatorLength a ≤ -Z.generatorLength b
    rw [hl a, hl b]
    linarith
  -- every product of the small generator with a kept one vanishes
  have hG : ∀ k i, Z.raghuramanGProdCora 2 (by norm_num [Z]) k i = 0 := by
    intro k i
    have hk : (k : ℕ) = 0 := by have := k.2; change k.val < 3 - 2 at this; omega
    fin_cases i <;>
      simp [Zonotope.raghuramanGProdCora, Zonotope.sortByLength, hsort, Z, dotProduct,
        Fin.sum_univ_succ]
  refine ⟨by norm_num [Z], fun i => hG _ i, ?_⟩
  simp [Zonotope.raghuramanAlphaMaxCora, hG]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
