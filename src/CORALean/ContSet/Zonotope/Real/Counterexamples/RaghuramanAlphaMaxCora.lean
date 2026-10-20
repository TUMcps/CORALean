module

public import CORALean.ContSet.Zonotope.Real.Operations.SortByLength

@[expose] public section

/-!
# `Zonotope.raghuramanGProdCora`, CORA's `G_prod` in the `'raghuraman'` reduction

CORA's `@zonotope/reduceUnderApprox.m`, `aux_reduceUnderApproxRaghuraman` (lines 260-281), up to
`G_prod = G_small'*G_big` (line 270): `aux_selectSmallestGenerators` (lines 625-645) sorts the
generators by decreasing squared length and splits them into the `eta_new` largest (`G_big`) and
the rest (`G_small`). Entry `(k, i)` is the product of the `k`-th small with the `i`-th big
generator, both in sorted order.

# `Zonotope.raghuramanAlphaMaxCora`, CORA's `alpha_max` in the `'raghuraman'` reduction

`[alpha_max,idx] = max(abs(G_prod),[],2)` (lines 271-272 of `@zonotope/reduceUnderApprox.m`): the
largest absolute alignment of each small generator with a kept one. Line 276 then divides
`G_prod(k, idx)` by it; at `alpha_max = 0` that is `0/0`, which MATLAB evaluates to `NaN`.

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

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA divides zero by zero in the Raghuraman reduction
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `G_prod` for `eta_new = etaNew` (`etaNew ≤ Z.h`). -/
noncomputable def Zonotope.raghuramanGProdCora (Z : Zonotope (Vec ℝ n)) (etaNew : ℕ)
    (hr : etaNew ≤ Z.h) : Fin (Z.h - etaNew) → Fin etaNew → ℝ :=
  -- [c,G_big,G_small] = aux_selectSmallestGenerators(Z,eta_new,'length')   (line 266)
  let Zs := Z.sortByLength
  let G_big := fun i : Fin etaNew =>
    Zs.G ⟨i, by have := i.2; simp only [Zs, Zonotope.sortByLength]; omega⟩
  let G_small := fun k : Fin (Z.h - etaNew) =>
    Zs.G ⟨etaNew + k, by have := k.2; simp only [Zs, Zonotope.sortByLength]; omega⟩
  -- G_prod = G_small'*G_big                                                (line 270)
  fun k i => dotProduct (G_small k) (G_big i)

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `alpha_max`, one entry per small generator. -/
noncomputable def Zonotope.raghuramanAlphaMaxCora (Z : Zonotope (Vec ℝ n)) (etaNew : ℕ)
    (hr : etaNew ≤ Z.h) : Fin (Z.h - etaNew) → ℝ :=
  let G_prod := Z.raghuramanGProdCora etaNew hr           -- G_prod = G_small'*G_big
  let alphas := fun k i => |G_prod k i|                   -- alphas = abs(G_prod)
  fun k => ⨆ i, alphas k i                                -- [alpha_max,idx] = max(alphas,[],2)

end CORALean.Real

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
